-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.centerExpr_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:12:15.781326+00:00
-- url     : https://prove2.me/submissions/24e1d516-880e-41a1-b959-8ca666dac7ca

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (j : Fin 3) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (centerExpr j).eval a z ρ = z j := rfl
end QEC.Coding.BDL26RandomPerturbation
