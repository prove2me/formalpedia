-- Prove2me | solution 1 for SQMeanEstimation.ring_l1_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T15:26:42.546227+00:00
-- url     : https://prove2.me/submissions/79b98752-3cc7-46f9-a5da-8d7fd9db7f5c

import Mathlib
import Definitions.Def_SQMeanEstimation_lqNorm
import Definitions.Def_SQMeanEstimation_posPart
import Definitions.Def_SQMeanEstimation_ringPart

open SQMeanEstimation in
theorem solution {d : ℕ} (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (j : ℕ) (w : Fin d → ℝ)
    (hw : lqNorm q w ≤ 1) :
    ∑ i, |ringPart j (SQMeanEstimation.posPart w) i| ≤
        ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) * ∑ i, |ringPart j (SQMeanEstimation.posPart w) i| ^ q ∧
      ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) * ∑ i, |ringPart j (SQMeanEstimation.posPart w) i| ^ q ≤
        ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) := by
  set b : ℝ := (2 : ℝ) ^ (-(j : ℝ) - 1) with hb
  have hbpos : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
  have hbeq : (2 : ℝ) ^ (-((j : ℝ) + 1)) = b := by rw [hb]; congr 1; ring
  have hcpos : 0 < b ^ (1 - q) := Real.rpow_pos_of_pos hbpos _
  have hcase : ∀ i, |ringPart j (SQMeanEstimation.posPart w) i| = 0 ∨ b < |ringPart j (SQMeanEstimation.posPart w) i| := by
    intro i
    unfold ringPart
    split_ifs with h
    · right; rw [← hbeq]; exact h.1
    · left; exact abs_zero
  have hle : ∀ i, |ringPart j (SQMeanEstimation.posPart w) i| ≤ |w i| := by
    intro i
    have h1 : |SQMeanEstimation.posPart w i| ≤ |w i| := by
      unfold SQMeanEstimation.posPart; split_ifs
      · exact le_rfl
      · rw [abs_zero]; exact abs_nonneg _
    unfold ringPart; split_ifs
    · exact h1
    · rw [abs_zero]; exact abs_nonneg _
  refine ⟨?_, ?_⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rcases hcase i with h0 | hpos
    · rw [h0, Real.zero_rpow (by linarith), mul_zero]
    · set x := |ringPart j (SQMeanEstimation.posPart w) i| with hx
      have hx0 : 0 < x := lt_trans hbpos hpos
      have e : x = x ^ q * x ^ (1 - q) := by
        rw [← Real.rpow_add hx0, show q + (1 - q) = 1 by ring, Real.rpow_one]
      have h2 : x ^ (1 - q) ≤ b ^ (1 - q) :=
        Real.rpow_le_rpow_of_nonpos hbpos hpos.le (by linarith)
      have h3 : 0 ≤ x ^ q := Real.rpow_nonneg hx0.le _
      calc x = x ^ q * x ^ (1 - q) := e
        _ ≤ x ^ q * b ^ (1 - q) := mul_le_mul_of_nonneg_left h2 h3
        _ = b ^ (1 - q) * x ^ q := mul_comm _ _
  · have hS : ∑ i, |w i| ^ q ≤ 1 := by
      by_contra hcon
      push_neg at hcon
      have := Real.one_lt_rpow hcon (show (0:ℝ) < 1 / q by positivity)
      unfold lqNorm at hw
      linarith
    have hT : ∑ i, |ringPart j (SQMeanEstimation.posPart w) i| ^ q ≤ 1 := by
      refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) hS
      exact Real.rpow_le_rpow (abs_nonneg _) (hle i) (by linarith)
    calc b ^ (1 - q) * ∑ i, |ringPart j (SQMeanEstimation.posPart w) i| ^ q ≤ b ^ (1 - q) * 1 :=
          mul_le_mul_of_nonneg_left hT hcpos.le
      _ = b ^ (1 - q) := mul_one _
