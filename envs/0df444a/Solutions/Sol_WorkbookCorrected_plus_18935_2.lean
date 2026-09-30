-- Prove2me | solution 2 for WorkbookCorrected.plus_18935
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T09:06:05.838088+00:00
-- url     : https://prove2.me/submissions/f27f6f29-5ca7-4bff-9713-e7cedf9ea235

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

theorem solution :
    (Real.logb 2 (4 * 251)) / (Real.logb 2 (2 * 5)) =
      (2 + Real.logb 2 251) / (1 + Real.logb 2 5) := by
  have h2 : Real.logb 2 2 = 1 := by
    simpa using (Real.logb_self_eq_one (show (1 : ℝ) < 2 by norm_num))
  have h4 : Real.logb 2 4 = 2 := by
    calc
      Real.logb 2 4 = Real.logb 2 (2 * 2) := by norm_num
      _ = Real.logb 2 2 + Real.logb 2 2 :=
        Real.logb_mul (by norm_num) (by norm_num)
      _ = 2 := by rw [h2]; norm_num
  calc
    Real.logb 2 (4 * 251) / Real.logb 2 (2 * 5)
        = (Real.logb 2 4 + Real.logb 2 251) /
          (Real.logb 2 2 + Real.logb 2 5) := by
            rw [Real.logb_mul (by norm_num) (by norm_num),
                Real.logb_mul (by norm_num) (by norm_num)]
    _ = (2 + Real.logb 2 251) / (1 + Real.logb 2 5) := by
      rw [h4, h2]
