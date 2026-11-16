-- Prove2me | solution 1 for QnAudit.log_factor_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:48:48.945852+00:00
-- url     : https://prove2.me/submissions/db5180cc-46e7-4588-9150-4dfd37076c51

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem solution (t : ℝ) (ht : 0 < t) (hsmall : t ≤ 1/2) :
    1 ≤ Real.log (2 + 1 / t ^ 2) := by
  have ht2 : 0 < t ^ 2 := pow_pos ht 2
  have htsq : t ^ 2 ≤ 1/4 := by nlinarith
  have hinv : 4 ≤ 1 / t ^ 2 := (le_div_iff₀ ht2).2 (by nlinarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    (by linarith : (4 : ℝ) ≤ 2 + 1 / t ^ 2)
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    simpa only [Nat.cast_ofNat, show (2 : ℝ)^2 = 4 by norm_num] using Real.log_pow (2 : ℝ) 2
  rw [hl4] at hlog
  linarith [Real.log_two_gt_d9]
