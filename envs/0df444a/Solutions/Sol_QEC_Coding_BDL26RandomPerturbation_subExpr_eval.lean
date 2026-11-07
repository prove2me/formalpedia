-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.subExpr_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:12:48.125307+00:00
-- url     : https://prove2.me/submissions/6ac7e419-3a68-4083-958d-7e4e2b009aee

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (b c : VecExpr) (a : Fin 3 → Space) (z : Space) (ρ : ℝ)
    (x y : Space) (hx : ∀ j, (b j).eval a z ρ = x j)
    (hy : ∀ j, (c j).eval a z ρ = y j) (j : Fin 3) :
    (subExpr b c j).eval a z ρ = (x-y) j := by
  change (b j).eval a z ρ-(c j).eval a z ρ = x j-y j
  rw [hx,hy]
end QEC.Coding.BDL26RandomPerturbation
