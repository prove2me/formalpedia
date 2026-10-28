-- Prove2me | solution 1 for TailOptCaching.ETLRU.optValue_le_value
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:00:10.83171+00:00
-- url     : https://prove2.me/submissions/be81f3a7-cc1a-4320-867f-576072a2d184

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal

open TailOptCaching.ETLRU in
theorem solution (P : Params) (π : Policy) (hπ : Admissible P π) (M k : ℕ)
    (z : State) :
    optValue P M z ≤ value P π M k z := by
  induction M generalizing k z with
  | zero => simp [optValue, value]
  | succ r ih =>
    rw [optValue, value]
    apply MeasureTheory.lintegral_mono
    intro d
    unfold arrivalExp
    apply Finset.sum_le_sum
    intro θ hθ
    have hθn : θ ≤ (decay d z).n := by
      rw [Finset.mem_range] at hθ; omega
    refine mul_le_mul_right ?_ _
    apply ENNReal.tsum_le_tsum; intro q
    refine mul_le_mul_right ?_ _
    apply ENNReal.tsum_le_tsum; intro a
    refine mul_le_mul_right ?_ _
    refine add_le_add_right ?_ _
    exact iInf₂_le_of_le _ (hπ k _ θ q a hθn) (ih (k + 1) _)
