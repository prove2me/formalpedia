-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.half_sum_norm_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:59.667982+00:00
-- url     : https://prove2.me/submissions/5325c900-8c1f-4541-ae84-a1a18b9945b8

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HalfSumNormSubSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open scoped ComplexConjugate
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution {n : ℕ} (a : Fin n → Fin n → ℂ) :
    (∑ j, ∑ k, ‖a j k - a k j‖ ^ 2) / 2 =
      ∑ j, ∑ k, ‖a k j‖ ^ 2 - (∑ j, ∑ k, a k j * conj (a j k)).re := by
  have h : ∀ j k, ‖a j k - a k j‖ ^ 2 =
      ‖a j k‖ ^ 2 + ‖a k j‖ ^ 2 - 2 * (a j k * conj (a k j)).re := by
    intro j k
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub]
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Complex.re_sum]
  have hs : ∑ j, ∑ k, ‖a j k‖ ^ 2 = ∑ j, ∑ k, ‖a k j‖ ^ 2 := Finset.sum_comm
  have hr : ∑ j, ∑ k, (a j k * conj (a k j)).re = ∑ j, ∑ k, (a k j * conj (a j k)).re :=
    Finset.sum_comm
  rw [hs, hr]
  ring
end ReciprocityTheory.L2DbarEstimates.E
