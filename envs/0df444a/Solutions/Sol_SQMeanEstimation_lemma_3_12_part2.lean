-- Prove2me | solution 1 for SQMeanEstimation.lemma_3_12_part2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:38:38.65733+00:00
-- url     : https://prove2.me/submissions/9bf4a05e-c88b-435a-90bb-585da4ddd746

import Mathlib
import Definitions.Def_SQMeanEstimation_lqNorm

open SQMeanEstimation in
theorem solution {d : ℕ} (p r : ℝ) (hp : 0 < p) (hpr : p < r) (x : Fin d → ℝ)
    (a : ℝ) (ha : 0 < a) (hax : ∀ i, x i ≠ 0 → a ≤ |x i|) :
    SQMeanEstimation.lqNorm p x ≤ a ^ (1 - r / p) * SQMeanEstimation.lqNorm r x ^ (r / p) := by
  unfold SQMeanEstimation.lqNorm
  have hr : 0 < r := by linarith
  have hp0 : p ≠ 0 := hp.ne'
  have hr0 : r ≠ 0 := hr.ne'
  have hterm : ∀ i, |x i| ^ p ≤ a ^ (p - r) * |x i| ^ r := by
    intro i
    by_cases hx : x i = 0
    · rw [hx, abs_zero, Real.zero_rpow hp0]
      exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg le_rfl _)
    · have hxa := hax i hx
      have hpos : 0 < |x i| := abs_pos.2 hx
      calc |x i| ^ p = |x i| ^ (p - r) * |x i| ^ r := by
            rw [← Real.rpow_add hpos]; ring_nf
        _ ≤ a ^ (p - r) * |x i| ^ r :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ha hxa (by linarith))
              (Real.rpow_nonneg hpos.le _)
  have hS0 : 0 ≤ ∑ i, |x i| ^ r := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hP0 : 0 ≤ ∑ i, |x i| ^ p := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hsum : ∑ i, |x i| ^ p ≤ a ^ (p - r) * ∑ i, |x i| ^ r := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hterm i)
  have e1 : (p - r) * (1 / p) = 1 - r / p := by field_simp
  have e2 : (1 / r) * (r / p) = 1 / p := by field_simp
  calc (∑ i, |x i| ^ p) ^ (1 / p) ≤ (a ^ (p - r) * ∑ i, |x i| ^ r) ^ (1 / p) :=
        Real.rpow_le_rpow hP0 hsum (by positivity)
    _ = (a ^ (p - r)) ^ (1 / p) * (∑ i, |x i| ^ r) ^ (1 / p) :=
        Real.mul_rpow (Real.rpow_nonneg ha.le _) hS0
    _ = a ^ (1 - r / p) * ((∑ i, |x i| ^ r) ^ (1 / r)) ^ (r / p) := by
        rw [← Real.rpow_mul ha.le, ← Real.rpow_mul hS0, e1, e2]
