-- Prove2me | solution 1 for PI.SqfRootShift.W.harm_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:30.480165+00:00
-- url     : https://prove2.me/submissions/844a6a70-f2bd-4f54-be7b-8ba41fb8cfe8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_ArithP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
namespace PI.SqfRootShift.W
theorem _root_.solution (r : ℕ) (hr : 1 ≤ r) : ∑ k ∈ Finset.Ioc 1 r, ((k : ℝ))⁻¹ ≤ Real.log r := by
  have h := harmonic_le_one_add_log r
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  rw [← Finset.add_sum_erase _ _ (Finset.left_mem_Icc.mpr hr), Finset.Icc_erase_left,
    Nat.cast_one, inv_one] at h
  linarith
end PI.SqfRootShift.W
