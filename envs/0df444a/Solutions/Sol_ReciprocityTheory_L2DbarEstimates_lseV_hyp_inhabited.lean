-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.lseV_hyp_inhabited
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:30:24.767411+00:00
-- url     : https://prove2.me/submissions/f42ab3e5-c15d-4b5d-b023-0878eb3ad5d9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviNonnegOn_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) :
    ∃ (U : Set (V n)) (u : Fin 1 → V n → ℝ), IsOpen U ∧ U.Nonempty ∧
      (∀ i, ∃ φ : V n → ℝ, ContDiffOn ℝ 2 φ U ∧ LeviNonnegOn n φ U ∧
        ∀ y ∈ U, u i y = Real.exp (φ y)) ∧ (∀ y ∈ U, 0 < ∑ i, u i y) :=
  ⟨Set.univ, fun _ _ => 1, isOpen_univ, Set.univ_nonempty,
    fun _ => ⟨fun _ => 0, contDiffOn_const, leviNonnegOn_const 0 _, fun _ _ => by simp⟩,
    fun _ _ => by simp⟩
end ReciprocityTheory.L2DbarEstimates
