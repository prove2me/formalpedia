-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.triangleQueryProgram_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:30.611783+00:00
-- url     : https://prove2.me/submissions/3ca5cf6f-39c4-4084-a610-2778d9450212

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution : triangleQueryProgram.cost ≤ 100000 := by decide
end QEC.Coding.BDL26RandomPerturbation
