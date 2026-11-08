-- Prove2me | solution 1 for SQMeanEstimation.lemma_3_12_part1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:30:47.630475+00:00
-- url     : https://prove2.me/submissions/02d540d2-56a3-45c2-972d-3d081bd3dee0

import Mathlib
import Definitions.Def_SQMeanEstimation_lqNorm

open SQMeanEstimation in
theorem solution {d : ℕ} (p r : ℝ) (hp : 0 < p) (hpr : p < r) (x : Fin d → ℝ) :
    lqNorm r x ≤ ‖x‖ ^ (1 - p / r) * lqNorm p x ^ (p / r) := by
  unfold lqNorm
  have hr : 0 < r := by linarith
  have hM : 0 ≤ ‖x‖ := norm_nonneg _
  have hB : 0 ≤ ∑ i, |x i| ^ p :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
  have hA : ∑ i, |x i| ^ r ≤ ‖x‖ ^ (r - p) * ∑ i, |x i| ^ p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hxi : |x i| ≤ ‖x‖ := by
      have := norm_le_pi_norm x i
      rwa [Real.norm_eq_abs] at this
    calc |x i| ^ r = |x i| ^ (r - p) * |x i| ^ p := by
          rw [← Real.rpow_add' (abs_nonneg _) (by rw [sub_add_cancel]; exact hr.ne'),
            sub_add_cancel]
      _ ≤ ‖x‖ ^ (r - p) * |x i| ^ p :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) hxi (by linarith))
            (Real.rpow_nonneg (abs_nonneg _) _)
  have e1 : (r - p) * (1 / r) = 1 - p / r := by field_simp
  have e2 : 1 / p * (p / r) = 1 / r := by field_simp
  calc (∑ i, |x i| ^ r) ^ (1 / r) ≤ (‖x‖ ^ (r - p) * ∑ i, |x i| ^ p) ^ (1 / r) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) hA
          (by positivity)
    _ = ‖x‖ ^ (1 - p / r) * ((∑ i, |x i| ^ p) ^ (1 / p)) ^ (p / r) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hM _) hB, ← Real.rpow_mul hM, ← Real.rpow_mul hB,
          e1, e2]
