-- Prove2me | solution 1 for SQMeanEstimation.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:56:36.237752+00:00
-- url     : https://prove2.me/submissions/1c76a6b6-e851-449d-a26c-367103dcc25f

import Mathlib
import Definitions.Def_SQMeanEstimation_lowPart

open SQMeanEstimation in
theorem solution {d : ℕ} (q n : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (hn : 0 < n) (j : ℕ)
    (u : Fin d → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∑ i, u i ≤ (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)) :
    ∑ i, |lowPart n u i| ^ q ≤ (4 / n) ^ (q - 1) * ∑ i, |lowPart n u i| ∧
      (4 / n) ^ (q - 1) * ∑ i, |lowPart n u i| ≤
        n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 3) * q - 3) := by
  have hc0 : 0 ≤ (4 / n) ^ (q - 1) := Real.rpow_nonneg (by positivity) _
  refine ⟨?_, ?_⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    unfold lowPart
    by_cases h : u i < 4 / n
    · rw [if_pos h, abs_of_nonneg (hu0 i)]
      have e : u i ^ q = u i ^ (q - 1) * u i := by
        have := Real.rpow_add' (hu0 i) (show (q - 1) + 1 ≠ 0 by linarith)
        rw [sub_add_cancel, Real.rpow_one] at this
        exact this
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (hu0 i)
      exact Real.rpow_le_rpow (hu0 i) h.le (by linarith)
    · rw [if_neg h, abs_zero, Real.zero_rpow (by linarith), mul_zero]
  · have h1 : ∑ i, |lowPart n u i| ≤ ∑ i, u i := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      unfold lowPart
      split_ifs
      · rw [abs_of_nonneg (hu0 i)]
      · rw [abs_zero]; exact hu0 i
    have e : (4 / n) ^ (q - 1) * (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1) =
        n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 3) * q - 3) := by
      rw [Real.div_rpow (by norm_num) hn.le]
      have h4 : (4:ℝ) ^ (q - 1) = (2:ℝ) ^ (2 * (q - 1)) := by
        rw [show (4:ℝ) = (2:ℝ) ^ (2:ℝ) by rw [Real.rpow_two]; norm_num,
          ← Real.rpow_mul (by norm_num)]
      have hn' : n ^ (1 - q) = (n ^ (q - 1))⁻¹ := by
        rw [← Real.rpow_neg hn.le, neg_sub]
      have h2 : (2:ℝ) ^ (2 * (q - 1)) * (2:ℝ) ^ (((j : ℝ) + 1) * q - 1) =
          (2:ℝ) ^ (((j : ℝ) + 3) * q - 3) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
      rw [h4, hn', div_eq_mul_inv,
        show (2:ℝ) ^ (2 * (q - 1)) * (n ^ (q - 1))⁻¹ * (2:ℝ) ^ (((j : ℝ) + 1) * q - 1) =
          (n ^ (q - 1))⁻¹ * ((2:ℝ) ^ (2 * (q - 1)) * (2:ℝ) ^ (((j : ℝ) + 1) * q - 1)) by ring, h2]
    calc (4 / n) ^ (q - 1) * ∑ i, |lowPart n u i|
        ≤ (4 / n) ^ (q - 1) * (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1) :=
          mul_le_mul_of_nonneg_left (h1.trans hu1) hc0
      _ = _ := e
