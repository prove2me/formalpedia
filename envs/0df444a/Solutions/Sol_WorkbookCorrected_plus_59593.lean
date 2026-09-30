-- Prove2me | solution 1 for WorkbookCorrected.plus_59593
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T07:17:17.800526+00:00
-- url     : https://prove2.me/submissions/399383e3-5c1e-4faf-b4cc-700b630b1340

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

theorem solution : (5 * Real.logb 3 2 + 2 * Real.logb 9 10) = (6 * Real.logb 3 2 + Real.logb 3 5) := by
  have h9 : Real.logb (9:ℝ) 10 = Real.log 10 / Real.log 9 := rfl
  have h3 : Real.logb (3:ℝ) 2 = Real.log 2 / Real.log 3 := rfl
  have h35 : Real.logb (3:ℝ) 5 = Real.log 5 / Real.log 3 := rfl
  have hong : Real.log 9 = 2 * Real.log 3 := by
    have : (9:ℝ) = 3^2 := by norm_num
    rw [this, Real.log_pow]; norm_num
  have : 2 * Real.logb 9 10 = Real.logb 3 2 + Real.logb 3 5 := by
    rw [h9, h3, h35, hong]
    have h3ne : Real.log 3 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    field_simp [h3ne]
    have : Real.log 2 + Real.log 5 = Real.log 10 := by
      have h := (Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0)).symm
      convert h using 2; norm_num
    linarith
  linarith
