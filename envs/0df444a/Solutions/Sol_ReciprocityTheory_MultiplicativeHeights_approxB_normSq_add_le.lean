-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_normSq_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:19:47.125422+00:00
-- url     : https://prove2.me/submissions/98b48807-286f-48fa-b965-19a124f90f21

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r : ℕ} (a b : Fin r → ℂ) :
    normSq (a + b) ≤ 2 * normSq a + 2 * normSq b := by
  unfold normSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [Pi.add_apply]
  have h1 : ‖a k + b k‖ ^ 2 ≤ (‖a k‖ + ‖b k‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  nlinarith [sq_nonneg (‖a k‖ - ‖b k‖)]
end ReciprocityTheory.MultiplicativeHeights
