-- Prove2me | solution 1 for Sendov.sinh_le_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:15:07.279967+00:00
-- url     : https://prove2.me/submissions/3e93efee-bfe7-498a-8053-4620cfe62d96

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_Sendov_Common_Sinh
import Theorems.Thm_Sendov_log_sinh_div_le

set_option autoImplicit false
open Sendov
open Real Set Filter
namespace Sendov
theorem _root_.solution {h : ℝ} (hh : 0 ≤ h) :
    sinh h ≤ h * exp (sqrt (h ^ 2 + 9) - 3) := by
  rcases eq_or_lt_of_le hh with rfl | hpos
  · simp
  · have hd : (0 : ℝ) < sinh h / h := div_pos (sinh_pos_iff.2 hpos) hpos
    grw [← (log_le_iff_le_exp hd).1 (log_sinh_div_le hpos)]
    field_simp
    simp
end Sendov
