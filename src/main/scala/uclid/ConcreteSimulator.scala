package uclid

import scala.util.parsing.combinator._
import scala.collection.mutable._
import scala.util.Random
import scala.math._

sealed trait CmdsMod
case object Fuzzing extends CmdsMod
case object Default extends CmdsMod
case object Panic extends CmdsMod


sealed abstract class ConcreteValue {
    def valueClone: ConcreteValue
}
case class ConcreteUndef () extends ConcreteValue {
    override def valueClone: ConcreteValue = new ConcreteUndef()
}
case class ConcreteBool (value: Boolean) extends ConcreteValue {
    override def toString = value.toString
    override def valueClone: ConcreteValue = new ConcreteBool(value)
} 
case class ConcreteInt (value: BigInt) extends ConcreteValue {
    override def toString = value.toString
    override def valueClone: ConcreteValue = new ConcreteInt(value)
} 
case class ConcreteBV (value: BigInt, width: Int) extends ConcreteValue {
    override def toString = f"${value.toString}bv${width.toString}"
    override def valueClone: ConcreteValue = new ConcreteBV(value, width)
} 

case class ConcreteArray (value: Map[List[ConcreteValue], ConcreteValue]) extends ConcreteValue {
    override def toString = value.toString
    override def valueClone = new ConcreteArray(value.clone)
}
case class ConcreteFunction (value: Map[List[ConcreteValue], ConcreteValue]) extends ConcreteValue {
    override def toString = value.toString
    override def valueClone = new ConcreteArray(value.clone)
} 
case class ConcreteRecord (value: Map[lang.Identifier, ConcreteValue]) extends ConcreteValue {
    override def toString = value.toString
    override def valueClone = new ConcreteRecord(value.clone)
} 
case class ConcreteEnum (ids: List[lang.Identifier], value: Int) extends ConcreteValue {
    override def toString = {
        if (value >=0) ids(value).toString
        else "Enum undefined"
    }
    override def valueClone = new ConcreteEnum(ids, value)
}

case class ConcreteSimulatorConfig (
    // TODO: combine with main debug
    // Configuration flags
    // var isPrintResult: Boolean = true,
    var isPrintDebug: Boolean = false,

    var cntInt      : Int = 0,
    var runtimeMod: CmdsMod = Panic,
    var jsonFileName : String = "",

    var seed : Long = 0
) {
    def setStepCount (cnt: Int) : Unit = { this.cntInt = cnt }
    // def printTrace (cmd: lang.GenericProofCommand) : Unit = { this.printTraceCmd = Some(cmd) }
    // def dontPrintTrace : Unit = { this.printTraceCmd = None }
}

case class ConcreteSimulatorStats (
    // Runtime statistics
    var terminate   : Boolean = false,
    var termStep    : Int = 0,
    var passCount   : Int = 0,
    var failCount   : Int = 0,
    var undetCount  : Int = 0
) {
    def setTermSig : Unit = { this.terminate = true } 
    def setTermStep (s: Int) : Unit = { this.termStep = s }
    def addPassCount : Unit = { this.passCount = passCount + 1 }
    def addFailCount : Unit = { this.failCount = failCount + 1 }
    def addUndetCount : Unit = { this.undetCount = undetCount + 1 }

    def refresh : Unit = {
        this.terminate = false
        this.termStep = 0
        this.passCount = 0
        this.failCount = 0
        this.undetCount = 0
    }
}

object ConcreteSimulator {

    val trace   : Map[BigInt, ConcreteContext] = Map[BigInt, ConcreteContext]()

    val stats   : ConcreteSimulatorStats = ConcreteSimulatorStats()
    val config  : ConcreteSimulatorConfig = ConcreteSimulatorConfig()
    // TODO: seed (allow user provided seed for reproucibility)?
    val random = new Random(config.seed)
    
    def printError (msg: String) : Unit = {
        UclidMain.printError(f"[ConcreteSimulator:ERROR] ${msg}")
        System.exit(1)
    }
    class SimulationError (msg:String = null, cause: Throwable=null) extends java.lang.RuntimeException(f"[ConcreteSimulatorERROR] ${msg}", cause)

    def printDebug(str: String){
        UclidMain.printVerbose(f"[ConcreteSimulator:DEBUG] ${str}")
    }

    def printResult(str: String){
        UclidMain.printResult(f"[ConcreteSimulator] ${str}")
    }

    def execute (module: lang.Module) : List[CheckResult] = {
        ConcreteSimulator.printResult("Starting simulation")
        
        module.cmds.foreach {
            cmd => cmd.name.toString match {
                case "concrete" => {
                    // Refresh statistics
                    stats.refresh
                    // Set configuration
                    config.setStepCount(cmd.args(0)._1.asInstanceOf[lang.IntLit].value.intValue())
                    
                    if (cmd.args.size == 2) {
                        // TODO: make these keywords
                        var (idArg,exprArg) = cmd.args(1);
                        idArg.toString match {
                            case "\"Default\"" => {
                                config.runtimeMod = Default
                            }
                            case "\"Random\"" => {
                                config.runtimeMod = Fuzzing
                            }
                            case _ => {}
                        }
                    }

                    // Execute the simulation
                    executeOne(module)

                    // Print the result
                    UclidMain.printResult("%d assertions passed.".format(stats.passCount))
                    UclidMain.printResult("%d assertions failed.".format(stats.failCount))
                    UclidMain.printResult("%d assertions indeterminate.".format(stats.undetCount))
                }
                case "print_concrete_trace" => {
                    printConcreteTrace(trace, cmd.args, cmd.argObj)
                }
                case _ => {}
            }
        }
        
        return List()
    }


    def executeOne (module: lang.Module) : Unit = {

        val concreteContext : ConcreteContext = new ConcreteContext()   
        concreteContext.extendVar(module.vars)
        concreteContext.extendInputVar(module.inputs)
        concreteContext.extendVar(module.outputs)
        concreteContext.extendFunction(module.functions)
        
        concreteContext.assignUndefVar(module.vars, false)
        concreteContext.assignUndefVar(module.inputs, true)

        module.init match {
            case Some(init) => simulate_stmt(concreteContext, init.body)
            case _ => {}
        }
        checkAssumes(module.axioms, concreteContext)
        checkProperties(module.properties, concreteContext)
        trace(0) = concreteContext.cloneObject
        
        if (stats.terminate) {
            stats.setTermStep(0)
            ConcreteSimulator.printResult("Terminated at step 0.")
        } else {
            ConcreteSimulator.printDebug(f"Running Concrete Simulation for ${config.cntInt} steps")
            val next_stmt = module.next match {
                case Some(next) => {
                    for (a <- 1 to config.cntInt) {
                        if (!stats.terminate) {
                            concreteContext.assignUndefVar(module.inputs,true)
                            simulate_stmt(concreteContext, next.body)
                            checkProperties(module.properties, concreteContext)
                            trace(a) = concreteContext.cloneObject
                        } else {
                            stats.setTermStep(a-1)
                            ConcreteSimulator.printDebug(s"Failed on iteration ${a-1}")
                        }
                    }
                }
                case _ => {}
            }
        }
    }


    def simulate_stmt (context: ConcreteContext, stmt: lang.Statement) : Unit = {
        stmt match {
            case lang.AssignStmt(lhss, rhss) => {
                val rhseval = rhss.map(rhs => evaluateExpr(context, rhs))
                (lhss zip rhseval).foreach{
                    case (lhssid, rhsval) => {
                        rhsval match {
                            case ConcreteUndef() => {
                                ConcreteSimulator.printDebug(f"Hit undefined value in AssignStmt for ${rhsval.toString}")
                            }
                            case _ => {}
                        }
                        ConcreteSimulator.printDebug(f"Assigned ${lhssid.toString} value ${rhsval.toString}")
                        context.updateVar(lhssid, rhsval)
                    }
                }
            }
            case lang.BlockStmt(vars, stmts) => {
                val flatVars : List[(lang.Identifier, lang.Type)] = vars.flatMap(v => v.ids.map(id => (id, v.typ)))
                context.extendVar(flatVars)
                context.assignUndefVar(flatVars, false)
                val oldContext = context.cloneObject
                stmts.foreach(s => simulate_stmt(context, s))
                context.removeExtraVar(flatVars,oldContext)
            }
            case lang.SkipStmt() => {}
            case lang.AssertStmt(e, id) => {
                ConcreteSimulator.printDebug("Evaluate AssertStmt "+e.toString)
                if (!evaluateBoolExpr(context, e)) { 
                    stats.addFailCount
                    stats.setTermSig
                    ConcreteSimulator.printResult("failed assert statement on:\n "+stmt)
                } else {
                    stats.addPassCount
                }
            }
            case lang.AssumeStmt(e, id) => {
                // TODO: check whether assume holds and report if it doesn't
            }
            case lang.HavocStmt(havocable) => throw new NotImplementedError(s"HavocStmt not implemented")
            case lang.IfElseStmt(cond, ifblock, elseblock) => {
                if (evaluateBoolExpr(context, cond)) {
                    simulate_stmt(context, ifblock)
                } else {
                    simulate_stmt(context, elseblock)
                }
            }
            case lang.ForStmt(id, typ, range, body) => {
                var low = evaluateExpr(context, range._1)
                var high = evaluateExpr(context, range._2)
                context.extendVar(List((id,typ)))
                typ match {
                    case lang.IntegerType() => {
                        val low_ = low match {
                            case l: ConcreteInt => l.value
                        }                        
                        val high_ = high match {
                            case h : ConcreteInt => h.value
                        }
                        for(it <- low_ to high_){
                            context.write(id, ConcreteInt(it))
                            simulate_stmt(context, body)
                        }
                    }
                    case lang.BitVectorType(w) => {
                        val low_ = low match{
                            case l: ConcreteBV  => l.value
                        }
                        val high_ = high match{
                            case h: ConcreteBV => h.value
                        }
                        for (it <- low_ to high_) {
                            context.write(id, ConcreteBV(it,w))
                            simulate_stmt(context, body)
                        }
                    }
                    case _ => throw new ConcreteSimulator.SimulationError(f"Does not support loop index of type ${typ.toString}")
                }
                context.removeVar(List((id,typ)))}
            case lang.WhileStmt(cond, body, invariants) => {
                while (evaluateBoolExpr(context, cond)) {
                    // TODO: set upper limit on while?
                    simulate_stmt(context, body)
                }
            }
            case lang.CaseStmt(body) => {
                throw new NotImplementedError("Unsupported CaseStmt in ConcreteSimulator.")
            }
            case lang.ProcedureCallStmt(id, callLhss, args, instanceId, moduleId) => {
                throw new NotImplementedError("Unsupported ProcedureCallStmt in ConcreteSimulator.")
            }
            case lang.MacroCallStmt(id) => {
                throw new NotImplementedError("Unsupported MacroCallStmt in ConcreteSimulator.")
            }
            case lang.ModuleCallStmt(id) => {
                throw new NotImplementedError("Unsupported ModuleCallStmt in ConcreteSimulator.")
            }
            case _ => {
                throw new NotImplementedError(f"Unsupported Statement: ${stmt} in ConcreteSimulator.")
            }
        }
    }
    
    def evaluateBoolExpr (context: ConcreteContext, cond: lang.Expr) : Boolean = {
            ConcreteSimulator.printDebug(f"Evaluating BoolExpr ${cond.toString}")
            evaluateExpr(context, cond) match {
                case ConcreteBool(b) => b
                // TODO: handle this simular to other undefs
                case ConcreteUndef() => {
                    //if we hit undef value, just give a false
                    //println("Hit a Undef Boolean")
                    true
                    // context.printVar(List())
                    // throw new Error("When Evaluation Bool value we hit a undefine value "+cond.toString)
                }
            }
        }

    def evaluateExpr (context: ConcreteContext, expr: lang.Expr) : ConcreteValue = {
        ConcreteSimulator.printDebug(f"Evaluating Expr: ${expr.toString}")
        expr match {
            case a : lang.Identifier => {
                context.read(a) match {
                    case ConcreteUndef() => ConcreteUndef()
                    case _ => context.read(a)
                }
            }
            case lang.BoolLit(b) => ConcreteBool(b)
            case lang.IntLit(b) => ConcreteInt(b)
            case lang.BitVectorLit(a,b) => ConcreteBV(a,b)
            case lang.OperatorApplication(op: lang.Operator, operands: List[lang.Expr]) => {
                if(op.isInstanceOf[lang.ForallOp]){
                    op match {
                        case lang.ForallOp(vs, patterns) => {
                            var retValue = true
                            if (vs.size > 1) {
                                throw new NotImplementedError("Unsupported ForallOp quantification with multiple variables.")
                            }
                            var (id, typ) = vs.head
                            context.extendVar(List((id,typ)))
                            typ match {
                                case lang.BitVectorType(w) => {
                                    // TODO: set limits on unrolling with warning/error?
                                    for (it <- 0 to (pow(2,w)-1).toInt) {
                                        context.write(id,ConcreteBV(it,w))
                                        retValue = retValue && evaluateBoolExpr(context, operands.head)
                                    }
                                }
                                case _ => throw new NotImplementedError(f"Unsupported loop index of type ${typ.toString}")
                            }
                            context.removeVar(List((id,typ)))
                            return ConcreteBool(retValue)
                        }
                        case _ => throw new ConcreteSimulator.SimulationError("Should not touch this line!")
                    }
                }
                
                // Unary operations
                if (operands.tail.size == 0) {
                    val operand_0 = evaluateExpr(context, operands.head)
                
                    operand_0 match{
                        case ConcreteBool(bool_0) => {
                            op match {
                                case lang.NegationOp() => ConcreteBool(!bool_0)
                                case _ => throw new ConcreteSimulator.SimulationError(f"Unsupported operator ${op.toString} for ConcreteBool.") 
                            }
                        }
                        case ConcreteInt(int_0) => {
                            op match {
                                case lang.IntUnaryMinusOp() => ConcreteInt(-int_0)
                                case _ => throw new ConcreteSimulator.SimulationError(f"Unsupported operator ${op.toString} for ConcreteBool.") 
                            }
                        }
                        case ConcreteBV(int_0, length) => {
                            op match {
                                case lang.ConcatOp() => throw new NotImplementedError("Unsupported operator ++ for ConcreteBV.")
                                case lang.BVNotOp(w) => ConcreteBV((~int_0) & ((1 << length) - 1), length)
                                case lang.BVUnaryMinusOp(w) => ConcreteBV((-int_0) & ((1 << length) - 1), length)
                                case lang.BVLeftShiftBVOp(w) => ConcreteBV((int_0 << w) & ((1 << length) - 1), length)
                                case lang.BVLRightShiftBVOp(w) => ConcreteBV((int_0 >> w) & ((1 << length) - 1), length)
                                case lang.BVARightShiftBVOp(w) => ConcreteBV((int_0 >> w) & ((1 << length) - 1) | (((1 << length) - 1) << w & ((1 << length) - 1)), length)
                                case lang.ConstExtractOp(slide) => ConcreteBV((int_0&((1 << (slide.hi+1) - 1)))>>slide.lo, slide.hi-slide.lo+1)
                                // TODO: whats up with this?
                                // case ConstBitVectorSlice(hi,lo) => ConcreteBV((int_0&((1 << (hi-lo)) - 1))>>lo, length)
                                // case VarBitVectorSlice(hi, lo, wd)
                                case _ => throw new NotImplementedError(f"Unsupported unary operator ${op.toString} for ConcreteBV.")
                            }
                            
                        }
                        case ConcreteArray(valuemap) => {
                            ConcreteSimulator.printDebug(f"Reading value from ConcreteArray: ${operands.head.toString}")
                            op match {
                                case lang.ArraySelect(indices) => {
                                    val eval_indices = indices.map(a => evaluateExpr(context,a))
                                    // TODO: too many debug prints
                                    // ConcreteSimulator.printDebug("\t With indices " + indices)
                                    // ConcreteSimulator.printDebug("\t With newMap " + eval_indices)
                                    // ConcreteSimulator.printDebug("\t With Return Value "+valuemap(eval_indices).toString)
                                    if (valuemap(eval_indices).isInstanceOf[ConcreteUndef]) {
                                        operands.head match{
                                            // TODO: This is too ad-hoc, should be handled in a more general way
                                            case id : lang.Identifier => {
                                                var fuzzingValue = context.runtimeValue(id, eval_indices)
                                                ConcreteSimulator.printDebug("We try to make a fuzzing Value "+fuzzingValue.toString)
                                                return fuzzingValue
                                            }
                                            case _ => throw new Error("Should not touch this line")
                                        }
                                        return valuemap(eval_indices)
                                    } else {
                                        return valuemap(eval_indices)
                                    }
                                }
                                case lang.ArrayUpdate(indices, value) => {
                                    val eval_value = evaluateExpr(context, value)
                                    val eval_indices = indices.map(a => evaluateExpr(context,a)) // list of concrete expr
                                    var old_map = valuemap // old array 
                                    old_map(eval_indices) = eval_value
                                    ConcreteArray(old_map)
                                }
                                // TODO: Any additional unary array operators should be handled here
                                case _ => throw new NotImplementedError(f"Unsupported unary operator ${op} for ConcreteArray.")
                            }
                        }
                        case ConcreteRecord(valuemap) => {
                            op match {
                                case lang.RecordSelect(id) =>{
                                    valuemap.get(id) match {
                                        case Some(value) => value
                                        case None => throw new ConcreteSimulator.SimulationError(f"Hit a undefined value ${id.toString}")
                                    }
                                }
                                case _ => throw new NotImplementedError(f"Unsupported unary operator ${op} for ConcreteRecord.")
                            }
                        }
                        case _ => throw new NotImplementedError(f"Unsupported operands ${operands} for unary operation ${op}") 
                    }            
                } 
                // Binary (and one ternary) operation
                else {
                    val operand_0 = evaluateExpr(context, operands.head)                
                    val operand_1 = evaluateExpr(context,operands.tail.head)
                    operand_0 match {
                        case ConcreteBool(bool_0) => {
                            operand_1 match {
                                case ConcreteBool(bool_1) => {
                                    op match{
                                        case lang.EqualityOp() => ConcreteBool(bool_0 == bool_1)
                                        case lang.InequalityOp() => ConcreteBool(bool_0 != bool_1)
                                        case lang.ConjunctionOp() => ConcreteBool(bool_0 && bool_1)
                                        case lang.DisjunctionOp() => ConcreteBool(bool_0 || bool_1)
                                        case lang.IffOp() => ConcreteBool(bool_0 == bool_1)
                                        case lang.ImplicationOp() => ConcreteBool(!bool_0 || bool_1)
                                        case _ => throw new NotImplementedError(f"Unsupported operator ${op.toString} for ConcreteBool.")
                                    }
                                }
                                case ConcreteUndef() => {
                                    throw new ConcreteSimulator.SimulationError(f"Hit undefined value for operand ${operands.tail.head.toString} in op ${op}")
                                }
                                case _ => {
                                    // TODO: Ternary operator has been mixed in!
                                    op match {
                                        case lang.ITEOp() => {
                                            if (bool_0) operand_1
                                            else evaluateExpr(context, operands.tail.tail.head)
                                        }
                                        case _ => throw new ConcreteSimulator.SimulationError(f"Unknown operator ${op} for expr ${expr}.")
                                    }
                                }
                            }
                        }
                        case ConcreteInt(int_0) => {
                            operand_1 match {
                                case ConcreteInt(int_1) => {
                                    op match{
                                        case lang.IntAddOp()=> ConcreteInt(int_0+int_1)
                                        case lang.IntSubOp() => ConcreteInt(int_0-int_1)
                                        case lang.IntMulOp() => ConcreteInt(int_0*int_1)
                                        case lang.IntDivOp() => ConcreteInt(int_0/int_1)
                                        case lang.IntLTOp() => ConcreteBool(int_0 < int_1)
                                        case lang.IntLEOp() => ConcreteBool(int_0 <= int_1)
                                        case lang.IntGEOp() => ConcreteBool(int_0 >= int_1)
                                        case lang.IntGTOp() => ConcreteBool(int_0 > int_1)
                                        case lang.InequalityOp() => ConcreteBool(int_0 != int_1)
                                        case lang.EqualityOp() => ConcreteBool(int_0 == int_1)
                                        case _ => throw new NotImplementedError(f"Unsupported operator ${op.toString} for ConcreteInt.")
                                    }
                                }
                                case ConcreteUndef() => {
                                    stats.addUndetCount
                                    if(config.isPrintDebug){
                                        // TODO: do we need this? We shouldn't have functions for debugging the ConcreteSimulator in the PR
                                        ConcreteSimulator.printDebug("Here we hit a undefine value: " + operands.head.toString)
                                        // context.printVar(List())
                                        // context.printInput(List())
                                    }
                                    ConcreteUndef()
                                }
                                case _ => throw new ConcreteSimulator.SimulationError(f"Operator ${op} applied to integer and ${expr.toString}")
                            }
                        }    
                        case ConcreteBV(int_0, length) => {
                            operand_1 match {
                                case ConcreteBV(int_1, length) => {
                                    val unint_0 = (~int_0) & ((1 << length) - 1)
                                    val unint_1 = (~int_0) & ((1 << length) - 1)
                                    op match {
                                        case lang.BVLTOp(w) => ConcreteBool(int_0 < int_1)
                                        case lang.BVLEOp(w) => ConcreteBool(int_0 <= int_1)
                                        case lang.BVGTOp(w) => ConcreteBool(int_0 > int_1)
                                        case lang.BVGEOp(w) => ConcreteBool(int_0 >= int_1)
                                        case lang.BVAddOp(w) => ConcreteBV((int_0 + int_1) & ((1 << length) - 1),w)
                                        case lang.BVSubOp(w) => ConcreteBV((int_0 - int_1) & ((1 << length) - 1),w) 
                                        case lang.BVMulOp(w) => ConcreteBV((int_0 * int_1) & ((1 << length) - 1),w)
                                        case lang.BVDivOp(w) => ConcreteBV((int_0 / int_1) & ((1 << length) - 1),w)
                                        case lang.BVAndOp(w) => ConcreteBV((int_0 & int_1) & ((1 << length) - 1),w)
                                        case lang.BVOrOp(w)  => ConcreteBV((int_0 | int_1) & ((1 << length) - 1),w)
                                        case lang.BVXorOp(w) => ConcreteBV((int_0 ^ int_1) & ((1 << length) - 1),w)
                                        case lang.BVSremOp(w) => ConcreteBV((int_0 % int_1) & ((1 << length) - 1),w)
                                        case lang.BVLTUOp(w) => ConcreteBool(unint_0 < unint_1)
                                        case lang.BVLEUOp(w) => ConcreteBool(unint_0 <= unint_1)
                                        case lang.BVGTUOp(w) => ConcreteBool(unint_0 > unint_1)
                                        case lang.BVGEUOp(w) => ConcreteBool(unint_0 >= unint_1)
                                        case lang.BVUremOp(w) => ConcreteBV(unint_0 % unint_1,w)
                                        case lang.BVUDivOp(w) => ConcreteBV(unint_0 / unint_1,w)
                                        case lang.EqualityOp() => ConcreteBool(int_0 == int_1)
                                        case lang.InequalityOp() => ConcreteBool(int_0 != int_1)
                                        case _ => throw new NotImplementedError(f"Unsupported operator ${op.toString} for ConcreteBV.")
                                    }
                                }
                                case ConcreteUndef() => {
                                    stats.addUndetCount
                                    ConcreteSimulator.printDebug("Here we hit a undefine value: "+operands.tail.head.toString)
                                    ConcreteUndef()
                                }
                                case _ => throw new ConcreteSimulator.SimulationError(f"Operator ${op} applied to BV and ${expr.toString}")
                            }
                        }
                        case ConcreteEnum(ids, index1) => {
                            operand_1 match {
                                case ConcreteEnum(ids2, index2) => {
                                    op match{
                                        case lang.EqualityOp() => ConcreteBool(index1 == index2)
                                        case lang.InequalityOp() => ConcreteBool(index1 != index2)
                                        case _ => throw new NotImplementedError(f"Unsupported operator ${op.toString} for ConcreteEnum.")
                                    }
                                }
                                case ConcreteUndef() => {
                                    stats.addUndetCount
                                    if (config.isPrintDebug) {
                                        // TODO: Handle this better?
                                        // TODO: We shouldn't have functions for debugging the ConcreteSimulator in the PR
                                        ConcreteSimulator.printDebug("Hit an undefined value: ${operands.head.toString}")
                                        // context.printVar(List())
                                        // context.printInput(List())
                                    }
                                    ConcreteUndef()
                                }
                            }
                        }
                        case ConcreteUndef() => {
                            ConcreteUndef()
                        }
                        case ConcreteArray(value_0) => {
                            operand_1 match{
                                case ConcreteArray(value_1) =>{
                                    op match{
                                        case lang.EqualityOp() => {
                                            var checkflag = true;
                                            for((index_0,v_0)<-value_0){
                                                checkflag = checkflag && (value_1(index_0)==v_0)
                                            }
                                            ConcreteBool(checkflag)
                                        }
                                        case _ => {
                                            throw new NotImplementedError("Invalid two operands"+expr)
                                        }
                                    }
                                }
                            }
                        }
                        case _ => {
                            throw new NotImplementedError("Does not support operation on this type of Expr: "+expr)
                        }
                    }
                }
                }
            case lang.FuncApplication(expr,args) => {
                expr match{
                    case id: lang.Identifier => {
                        // List of concrete expr
                        val eval_args = args.map(a => evaluateExpr(context,a)) 
                        context.read(id) match{
                            case ConcreteFunction(valueMap) => {
                                var retValue = valueMap(eval_args)
                                if (retValue.isInstanceOf[ConcreteUndef]) {
                                    retValue = context.runtimeValue(id,eval_args)
                                    ConcreteSimulator.printDebug(f"We make a fuzzing Value for Function ${retValue.toString}")
                                }
                                retValue
                            }
                            case _ => {
                                ConcreteUndef()
                            }
                        }
                    }
                    case _ => {
                      throw new NotImplementedError(s"Expression evaluation for ${expr}.")  
                    }
                }
            }
            case _ => throw new NotImplementedError(s"Expression evaluation for ${expr}.")
        }
    }


    def generateValue (cValue: ConcreteValue, uclidType: lang.Type, isInput: Boolean) : ConcreteValue = {
        ConcreteSimulator.printDebug(f"Generating value for uclidType ${uclidType.toString}")  
        cValue match{
            case ConcreteUndef() =>{
                uclidType match{
                    case lang.IntegerType() => {
                        config.runtimeMod match{
                            case Fuzzing => ConcreteInt(random.nextInt())
                            case Default => ConcreteInt(0)
                            case _ => ConcreteUndef()
                        }   
                    }
                    case lang.BooleanType() => {
                        config.runtimeMod match{
                            case Fuzzing => ConcreteBool(random.nextBoolean())
                            case Default => ConcreteBool(false)
                            case _ => ConcreteUndef()
                        }
                    }
                    case lang.BitVectorType(w)   =>  {
                        config.runtimeMod match{
                            case Fuzzing => return ConcreteBV(random.nextInt(pow(2,w).toInt), w)
                            case Default => ConcreteBV(0,w)
                            case _ => ConcreteUndef()
                        }
                    }
                    case lang.EnumType (ids) =>{
                        config.runtimeMod match{
                            case Fuzzing => ConcreteEnum(ids, random.nextInt(ids.size))
                            case Default => ConcreteEnum(ids, 0)
                            case _ => ConcreteEnum(ids,-1)
                        }
                    } 
                    case _ => throw new ConcreteSimulator.SimulationError(f"NotImplemented: generateValue does not support type ${uclidType}") 
                }
            }
            case ConcreteBool(b) =>{
                if(isInput){
                    config.runtimeMod match{
                        case Fuzzing => ConcreteBool(random.nextBoolean())
                        case Default => ConcreteBool(false)
                        case _ => ConcreteBool(b)
                    }
                }
                else
                    ConcreteBool(b)
            }
            case ConcreteInt(v) =>  {
                if(isInput){
                    config.runtimeMod match{
                        case Fuzzing => ConcreteInt(random.nextInt())
                        case Default => ConcreteInt(0)
                        case _ => ConcreteInt(v)
                    }   
                }
                else
                    ConcreteInt(v)
            }
            case ConcreteBV(v,w)   =>  {
                if(isInput){
                    config.runtimeMod match{
                        case Fuzzing => ConcreteBV(random.nextInt(pow(2,w).toInt),w)
                        case Default => ConcreteBV(0,w)
                        case _ => ConcreteBV(v,w)
                    }
                }    
                else
                    ConcreteBV(v,w)
            }
            case ConcreteRecord(members) =>{
                uclidType match{
                    case lang.RecordType(members) => {
                        var RecordMap = scala.collection.mutable.Map[lang.Identifier, ConcreteValue]()
                        for ((mem_id,mem_typ) <- members) {
                            mem_typ match{
                                case lang.IntegerType() => {
                                    config.runtimeMod match{
                                        case Fuzzing => RecordMap(mem_id) = ConcreteInt(random.nextInt())
                                        case Default => RecordMap(mem_id) = ConcreteInt(0)
                                        case _ => RecordMap(mem_id) = ConcreteUndef()
                                    }
                                }
                                
                                case lang.BooleanType() => {
                                    config.runtimeMod match{
                                        case Fuzzing => RecordMap(mem_id) = ConcreteBool(random.nextBoolean())
                                        case Default => RecordMap(mem_id) = ConcreteBool(false)
                                        case _ => RecordMap(mem_id) = ConcreteUndef()
                                    }
                                }
                                case lang.BitVectorType(w) => {
                                    config.runtimeMod match{
                                        case Fuzzing => RecordMap(mem_id) = ConcreteBV(random.nextInt(pow(2,w).toInt),w)
                                        case Default => RecordMap(mem_id) = ConcreteBV(0,w)
                                        case _ => RecordMap(mem_id) = ConcreteUndef()
                                    }
                                }
                                case lang.EnumType(ids) => {
                                    config.runtimeMod match{
                                        case Fuzzing => ConcreteEnum(ids,random.nextInt(ids.size))
                                        case Default => ConcreteEnum(ids,0)
                                        case _ => ConcreteEnum(ids,-1)
                                    }
                                }   
                                case _ => throw new SimulationError(f"NotImplemented: generateValue ConcreteRecord does not support type ${mem_typ.toString}")
                            }
                        }
                        ConcreteRecord(RecordMap)
                    }
                    case _ => throw new SimulationError(f"generateValue record with incorrect type")
                }
            }
            case ConcreteArray(varMap) =>{
                cValue
            }
            case _ => cValue
        }    
    }
    
    def checkAssumes (assumes: List[lang.AxiomDecl], context: ConcreteContext) {
        for (assume <- assumes) {
            if (!evaluateBoolExpr(context, assume.expr)) { 
                stats.addFailCount
                stats.setTermSig
                ConcreteSimulator.printResult(f"Failed assume statement ${assume.toString}.")
                // TODO: handle this better
                // context.printVar(List())
                // context.printInput(List())
                throw new ConcreteSimulator.SimulationError("Failed on assume, please try different seed/input strategy.")
            } else {
                stats.addPassCount
            }
        }
    }

    def checkProperties (properties: List[lang.SpecDecl], context: ConcreteContext) {
        for (property <- properties){
            ConcreteSimulator.printDebug(f"Checking property ${property.toString}")
            if (!evaluateBoolExpr(context, property.expr)) { 
                stats.addFailCount
                stats.setTermSig
                ConcreteSimulator.printResult("failed assert statement in"+property.toString)
            } else {
                stats.addPassCount
            }
        }
    }

    def printVars (context: ConcreteContext, vars: List[(lang.Expr, String)]) : Unit = {
        if (vars.isEmpty) {
            println("\tVarmap:")
            for ((key,value) <- context.varMap){
                println(s"${key.toString}: ${value.toString}")
            }
            println("\n")
        }
        for (variable <- vars){
            println(variable._1 + ":  " + evaluateExpr(context, variable._1).toString)
        }
    }
    
    def printConcreteTrace(trace:Map[BigInt,ConcreteContext],exprs : List[(lang.Expr, String)], arg : Option[lang.Identifier]){
        UclidMain.printStatus(f"Generated trace of length ${stats.termStep}")
        UclidMain.printStatus("=================================")
        ConcreteSimulator.printDebug(f"Terminated at step ${stats.termStep}")
        ConcreteSimulator.printDebug("The trace's size is "+trace.size)
        for (a <- 0 to stats.termStep) {
            if (a <= stats.termStep) {
                UclidMain.printStatus("=================================")
                UclidMain.printStatus(f"Step # ${a.toString}")
                printVars(trace(a), exprs)
                UclidMain.printStatus("=================================")
            }
        }
    }
}


case class ConcreteContext() {
    var varMap: scala.collection.mutable.Map[lang.Identifier, ConcreteValue] = collection.mutable.Map()
    var varTypeMap: scala.collection.mutable.Map[lang.Identifier, lang.Type] = collection.mutable.Map()
    var inputMap: scala.collection.mutable.Map[lang.Identifier, ConcreteValue] = collection.mutable.Map()
    var outputMap: scala.collection.mutable.Map[lang.Identifier, ConcreteValue] = collection.mutable.Map()
    
    def read (variable: lang.Identifier) : ConcreteValue = {
        if (varMap.contains(variable)) varMap(variable)
        else if (inputMap.contains(variable)) inputMap(variable)
        else ConcreteUndef()
    }
    def write (variable: lang.Identifier, value: ConcreteValue) {
        if (varMap.contains(variable)) varMap(variable) = value
        else if (inputMap.contains(variable)) inputMap(variable) = value
        else ConcreteSimulator.printError(f"Variable ${variable.toString} not found in context")
    }
    def updateVar (lhs: lang.Lhs, value: ConcreteValue) {
        ConcreteSimulator.printDebug(f"Update ${lhs.toString} with value ${value.toString}")
        lhs match {
            case lang.LhsId(id) => {
                varMap(id) = value
            }
            case lang.LhsArraySelect(id, indices) => {
                varMap(id) match {
                    case ca: ConcreteArray => {
                        // List of concrete indices expressions 
                        val eval_indices = indices.map(a => ConcreteSimulator.evaluateExpr(this, a)) 
                        var old_map = ca.value
                        old_map(eval_indices) = value
                        val new_arr = ConcreteArray(old_map)
                        varMap(id) = new_arr
                    }
                    case _ => 
                        ConcreteSimulator.printError(f"Attempting ArraySelect on a non-array object ${id.name}")
                }
            }
            case lang.LhsRecordSelect(id, fieldid) => {
                ConcreteSimulator.printDebug(s"Updating: record ${id.toString}, fieldid ${fieldid}")
                varMap(id) = updateRecordValue(fieldid, value, varMap(id))  
            }
            case _ => {
                ConcreteSimulator.printError(s"Unimplemented: LHS update for ${lhs}")
            }
        }
    }

    def extendVar (vars: List[(lang.Identifier, lang.Type)]) : Unit = {
        for ((id,typ) <- vars) {
            varTypeMap(id) = typ
        }
        var enumContext = collection.mutable.Map[lang.Identifier, ConcreteValue]()
        val newContext = collection.mutable.Map[lang.Identifier, ConcreteValue](
            vars.map(v => v._2 match {
                case lang.IntegerType() => {
                    (v._1, ConcreteUndef())
                }
                case lang.BooleanType() => {
                    (v._1, ConcreteUndef())
                }
                case lang.BitVectorType(w) => {
                    (v._1, ConcreteUndef())
                }
                case lang.ArrayType(inType, outType) => {
                    // TODO: outType could be complex type like another array or record
                    (v._1, ConcreteArray(scala.collection.mutable.Map[List[ConcreteValue], ConcreteValue]().withDefaultValue(ConcreteUndef())))
                }
                case lang.RecordType(members) => {
                    for ((memberId,memberType) <- members) {
                        memberType match{
                            case lang.EnumType(ids) => {
                                for ((id,i) <- ids.view.zipWithIndex) {
                                    enumContext(id) = ConcreteEnum(ids, i)
                                }
                                // TODO: Should this be ConcreteUndef?
                                (v._1, ConcreteEnum(ids, -1))
                            }
                            case _ => {

                            }
                        }
                    }
                    (v._1, ConcreteRecord(scala.collection.mutable.Map(members.map(m => (m._1, ConcreteUndef())): _*)))
                }
                case lang.EnumType(ids) => {
                    for ((id,i) <- ids.view.zipWithIndex) {
                        enumContext(id) = ConcreteEnum(ids, i)
                    }
                    (v._1, ConcreteEnum(ids, -1))
                }
                case lang.UninterpretedType(name) =>{
                    throw new NotImplementedError(f"UninterpretedType ${name.toString} has not been support yet")
                }
                case _ => {
                    throw new NotImplementedError(f"${v.toString} has not been supported yet!")
                }
            }) : _*
        )
        varMap = varMap.++(enumContext);
        varMap = varMap.++(newContext);}
    def extendFunction (functionDecls: List[lang.FunctionDecl]) : Unit = {
        for(functionDecls<-functionDecls){
            val id = functionDecls.id
            val funcArg = functionDecls.sig.args
            val retType = functionDecls.sig.retType
            varTypeMap(id) = retType;
            varMap(id) = ConcreteFunction(scala.collection.mutable.Map[List[ConcreteValue], ConcreteValue]().withDefaultValue(ConcreteUndef()))
        }
    }
    def removeVar (vars: List[(lang.Identifier, lang.Type)]) : Unit = {
        for ((variableName, variableType) <- vars) {
            varMap.-(variableName)
        }
    }

    def assignUndefVar(vars: List[(lang.Identifier, lang.Type)], isInput: Boolean) : Unit = {
        // TODO: this is dangerous code editing same map that is being looped over
        if (isInput) {
            var retContext = inputMap;
            for ((key, value) <- inputMap){     
                for ((id,typ) <- vars){
                    if (key == id) {
                        retContext(key) = ConcreteSimulator.generateValue(value,typ,isInput)
                    }
                }
            }
            inputMap = retContext
        } else {
            // Loop over the context and assign good value according its type
            var retContext = varMap;
            // check the varMap
            for ((key, value) <- varMap){     
                for((id,typ) <- vars){
                    if(key == id){
                        retContext(key) = ConcreteSimulator.generateValue(value,typ,isInput)
                    }
                }
            }
            varMap = retContext
        }
    }
    
    def cloneObject: ConcreteContext ={
        var clone = new ConcreteContext();
        for((key,value)<-varMap){
            clone.varMap(key) = value.valueClone;
        }
        for((key,value)<-inputMap){
            clone.inputMap(key) = value.valueClone;
        }
        for((key,value)<-outputMap){
            clone.outputMap(key)= value.valueClone;
        }
        clone
    }

    def removeExtraVar (vars: List[(lang.Identifier, lang.Type)], oldContext: ConcreteContext) : Unit = {
        for (id <- vars) {
            varMap.-(id._1)
            if (oldContext.varMap.contains(id._1)) {
                varMap += (id._1->oldContext.varMap(id._1))
            }
        }
    }

    def extendInputVar (vars: List[(lang.Identifier, lang.Type)]) : Unit= {
        // TODO: this is bad code, why not use an inbuilt operation as:
        // varTypeMap = varTypeMap.++(vars)
        for ((id,typ) <- vars) {
            varTypeMap(id) = typ
        }
        var returnContext = inputMap
        var enumContext = collection.mutable.Map[lang.Identifier, ConcreteValue]()
        val newContext = collection.mutable.Map[lang.Identifier, ConcreteValue](
            vars.map(v => v._2 match {
                case lang.IntegerType() => {
                    (v._1, ConcreteUndef())
                }
                case lang.BooleanType() => {
                    (v._1, ConcreteUndef())
                }
                case lang.BitVectorType(w) => {
                    (v._1, ConcreteUndef())
                }
                //... fill in
                case lang.ArrayType(inType, outType) => {
                    // TODO: outType could be complex type like another array or record
                    (v._1, ConcreteArray(scala.collection.mutable.Map[List[ConcreteValue], ConcreteValue]().withDefaultValue(ConcreteUndef())))
                }
                case lang.RecordType(members) => {
                    val RecordMap = scala.collection.mutable.Map[lang.Identifier, ConcreteValue]();
                    for(member<-members){
                        RecordMap(member._1)=ConcreteUndef();
                    }
                    (v._1, ConcreteRecord(RecordMap))
                }
                case lang.EnumType(ids) => {
                    for((id,i)<-ids.view.zipWithIndex){
                        enumContext(id)=ConcreteEnum(ids,i)
                    };
                    (v._1,ConcreteEnum(ids,-1))
                }   
                case _ => {
                    throw new NotImplementedError(v.toString+" has not been support yet!")
                }
            }) : _*)
            
        returnContext = returnContext.++(newContext)
        returnContext = returnContext.++(enumContext)
        inputMap = returnContext
    }
    
    //In runtime, we hit a undefine value, we can generate a new value for it
    def runtimeValue(id:lang.Identifier,index:List[ConcreteValue]): ConcreteValue={
        varTypeMap(id) match{
            case lang.ArrayType(inTypes,outType)=>{

                //So outType is a Uclid Type
                var newValue = ConcreteSimulator.generateValue(ConcreteUndef(), outType, false);
                ConcreteSimulator.printDebug("We make a fuzzing Value "+newValue.toString)
                varMap(id) match{
                    case ConcreteArray(arraymap) =>{
                        arraymap(index) = newValue
                        return newValue
                    }
                    case _ => throw new Error("Should not touch this place")
                }
            }
            case _ =>{
                //it can be function call as well
                varMap(id) match{
                    case ConcreteFunction(functionMap) =>{
                        var newValue = ConcreteSimulator.generateValue(ConcreteUndef(),varTypeMap(id),false);
                        functionMap(index) = newValue
                        varMap(id) = ConcreteFunction(functionMap)
                        newValue
                    }
                    case _ => ConcreteUndef()
                }
            }
        }
    }
    
    //private Functions
    def updateRecordValue(fields: List[lang.Identifier], value: ConcreteValue, 
        recordValue: ConcreteValue) : ConcreteRecord = {
        if (fields.size == 1) {
            recordValue match {
                case ConcreteUndef() => ConcreteRecord(Map(fields.head -> value))
                case ConcreteRecord(map) => {
                    map(fields.head) = value
                    ConcreteRecord(map)
                }
                case _ => throw new NotImplementedError(s"UpdateRecord applied to non-Record type")
            }
        } else {
            // now, we have one recordValue and we have not touch the end of the Record
            recordValue match{
                case ConcreteUndef() => 
                    ConcreteRecord(Map(fields.head->updateRecordValue(fields.tail, value, ConcreteUndef())))
                case ConcreteRecord(map) => {
                    val newrec = updateRecordValue(fields.tail, value, map(fields.head))
                    map(fields.head) = newrec
                    ConcreteRecord(map)
                }
                case _ => throw new NotImplementedError(s"UpdateRecord applied to non-Record type")
            }
        }
    }        
}