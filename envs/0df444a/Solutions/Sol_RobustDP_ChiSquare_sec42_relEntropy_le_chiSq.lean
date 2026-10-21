-- Prove2me | solution 1 for RobustDP.ChiSquare.sec42_relEntropy_le_chiSq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:26:48.485041+00:00
-- url     : https://prove2.me/submissions/488d2e17-ca3b-413f-b897-31ea524fe64b

import Mathlib
import Definitions.Def_RobustDP_ChiSquare_Moments
import Definitions.Def_RobustDP_ChiSquare_ChiSqSet
import Definitions.Def_RobustDP_ChiSquare_RelEntropy

set_option autoImplicit false
open RobustDP.ChiSquare

theorem solution {S : Type*} [Fintype S] (p q : S → ℝ)
    (hp : p ∈ stdSimplex ℝ S) (hq : q ∈ stdSimplex ℝ S) (hq_pos : ∀ s, 0 < q s) :
    relEntropy p q ≤ ∑ s, p s * ((p s - q s) / q s) ∧
      ∑ s, p s * ((p s - q s) / q s) = chiSqDist p q := by
  constructor
  · unfold relEntropy
    apply Finset.sum_le_sum
    intro s _
    rcases (hp.1 s).eq_or_lt with h | h
    · simp [← h]
    · have h1 := Real.log_le_sub_one_of_pos (div_pos h (hq_pos s))
      calc p s * Real.log (p s / q s) ≤ p s * (p s / q s - 1) :=
            mul_le_mul_of_nonneg_left h1 h.le
        _ = p s * ((p s - q s) / q s) := by
            field_simp [(hq_pos s).ne']
  · unfold chiSqDist
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    have key : ∀ s, p s * ((p s - q s) / q s) - (p s - q s) ^ 2 / q s = p s - q s := by
      intro s
      field_simp [(hq_pos s).ne']
      ring
    simp_rw [key]
    rw [Finset.sum_sub_distrib, hp.2, hq.2]
    simp
