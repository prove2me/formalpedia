-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.vertexExpr_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:12:14.921562+00:00
-- url     : https://prove2.me/submissions/adc29748-a76d-4061-8508-78c49f98dfb5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (i j : Fin 3) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (vertexExpr i j).eval a z ρ = a i j := rfl
end QEC.Coding.BDL26RandomPerturbation
