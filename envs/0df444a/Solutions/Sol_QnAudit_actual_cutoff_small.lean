-- Prove2me | solution 1 for QnAudit.actual_cutoff_small
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:54:26.208177+00:00
-- url     : https://prove2.me/submissions/2debcfef-3c65-40d0-88dd-b1c5b2ec34b6

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem solution :
    1 / Real.sqrt ((3000000000000 : ℝ)^2 - 1/4) ≤ 1/4 := by
  have ha : (0 : ℝ) ≤ (3000000000000 : ℝ)^2 - 1/4 := by norm_num
  have hs := Real.sq_sqrt ha
  have hsn := Real.sqrt_nonneg ((3000000000000 : ℝ)^2 - 1/4)
  have hlarge : 4 ≤ Real.sqrt ((3000000000000 : ℝ)^2 - 1/4) := by nlinarith
  apply (div_le_iff₀ (by linarith : 0 < Real.sqrt ((3000000000000 : ℝ)^2 - 1/4))).2
  linarith
