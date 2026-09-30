-- Prove2me | solution 1 for WorkbookCorrected.plus_29456
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T07:01:43.440372+00:00
-- url     : https://prove2.me/submissions/19d802a1-8244-4000-8fb3-1c101c27a7d9

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

theorem solution : Real.logb 3 (90 - 3 ^ 4) * Real.logb 2 (76 - 44) * Real.logb 6 (1421 - 5 ^ 3) = 40 := by
  have h1 : (90 - 3 ^ 4 : ℝ) = 3 ^ 2 := by norm_num
  have h2 : (76 - 44 : ℝ) = 2 ^ 5 := by norm_num
  have h3 : (1421 - 5 ^ 3 : ℝ) = 6 ^ 4 := by norm_num
  rw [h1, h2, h3, Real.logb_pow, Real.logb_pow, Real.logb_pow]
  have a : Real.logb (3:ℝ) 3 = 1 := Real.logb_self_eq_one (by norm_num)
  have b : Real.logb (2:ℝ) 2 = 1 := Real.logb_self_eq_one (by norm_num)
  have c : Real.logb (6:ℝ) 6 = 1 := Real.logb_self_eq_one (by norm_num)
  simp [a, b, c]
  norm_num
