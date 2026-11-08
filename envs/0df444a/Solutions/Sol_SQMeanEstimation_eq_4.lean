-- Prove2me | solution 1 for SQMeanEstimation.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:25:30.216199+00:00
-- url     : https://prove2.me/submissions/32f2f2dc-10e1-4a9f-95d3-0c7003d9bc53

import Mathlib
import Definitions.Def_SQMeanEstimation_highPart

open SQMeanEstimation in
theorem solution {d : ℕ} (q n : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (hn : 0 < n) (j : ℕ)
    (u : Fin d → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∑ i, u i ≤ (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)) :
    ∑ i, |highPart n u i| ^ (q / 2) ≤ (1 / n) ^ (q / 2 - 1) * ∑ i, |highPart n u i| ∧
      (1 / n) ^ (q / 2 - 1) * ∑ i, |highPart n u i| ≤
        n ^ (1 - q / 2) * (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1) := by
  have hn1 : (0 : ℝ) < 1 / n := one_div_pos.mpr hn
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    unfold highPart
    split_ifs with h
    · rw [abs_of_nonneg (hu0 i)]
      have hx : 0 < u i := lt_of_lt_of_le hn1 h
      calc u i ^ (q / 2) = u i ^ (q / 2 - 1) * u i := by
            rw [← Real.rpow_add_one hx.ne', sub_add_cancel]
        _ ≤ (1 / n) ^ (q / 2 - 1) * u i :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hn1 h (by linarith))
              (hu0 i)
    · rw [abs_zero, Real.zero_rpow (ne_of_gt (by linarith)), mul_zero]
  · have e : (1 / n) ^ (q / 2 - 1) = n ^ (1 - q / 2) := by
      rw [one_div, Real.inv_rpow hn.le, ← Real.rpow_neg hn.le]
      congr 1; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn.le _)
    refine le_trans ?_ hu1
    apply Finset.sum_le_sum
    intro i _
    unfold highPart
    split_ifs
    · rw [abs_of_nonneg (hu0 i)]
    · rw [abs_zero]; exact hu0 i
