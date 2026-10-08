-- Prove2me | solution 1 for PiIrrationality.salikhov_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T09:30:16.925798+00:00
-- url     : https://prove2.me/submissions/398ca5e3-9d72-4a12-8185-a45d41cf9c4d

import Definitions.Def_PiIrrationality_UpperBound
import Theorems.Thm_PiIrrationality_ZZEven_upperBound_of_saving
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

theorem solution : PiIrrationality.UpperBound (7.606309 : ℝ) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have hlam : (∑ k ∈ Finset.range 3, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) = (71 / 60 : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have ht : (0 : ℝ) < 5 * Real.log 2 - 1 - 10 * (1 / 1000) + (71 / 60 : ℝ) := by norm_num at h1 ⊢; linarith
  have hg : (0 : ℝ) < 5 * Real.log 2 - 102 / 100 - 11 * (1 / 1000) + (71 / 60 : ℝ) := by
    norm_num at h1 ⊢; linarith
  apply PiIrrationality.ZZEven.upperBound_of_saving 3 (1 / 1000) 7.606309 hδ
  · rw [hlam]; norm_num at h2 ⊢; linarith
  · rw [hlam]; exact hg
  · rw [hlam]
    have : (2522 / 100 + 10 * (1 / 1000) - Real.log 2 - (71 / 60 : ℝ)) /
        (5 * Real.log 2 - 1 - 10 * (1 / 1000) + (71 / 60 : ℝ)) ≤ 7.606309 - 1 := by
      rw [div_le_iff₀ ht]; norm_num at h1 h2 ⊢; nlinarith
    linarith
  · rw [hlam]
    have : (2522 / 100 + 10 * (1 / 1000) - Real.log 2 - (71 / 60 : ℝ)) /
        (5 * Real.log 2 - 102 / 100 - 11 * (1 / 1000) + (71 / 60 : ℝ)) ≤ 7.606309 - 1 := by
      rw [div_le_iff₀ hg]; norm_num at h1 h2 ⊢; nlinarith
    linarith
