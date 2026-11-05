-- Prove2me | solution 1 for Pr73ProfileReal.row_exp_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/73a6db7a-692e-4d27-a4e0-e3770d6fe78e

import Definitions.Def_Pr73ProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Pr73ProfileReal
import Theorems.Thm_Pr73ProfileReal_row_valid
import Theorems.Thm_Pr73ProfileReal_row_log_upper
import Theorems.Thm_AnalyticEnclosures_exp_le_of_expUpper


set_option autoImplicit true
open Pr73ProfileReal
open AnalyticEnclosures Pr73ProfileCertificate
namespace Pr73ProfileReal
theorem _root_.solution (r : Row) (hr : r ∈ rows) :
    Real.exp ((saving : ℝ) * Real.log ((m : ℝ) / r.width)) ≤ (r.upper : ℝ) := by
  rcases row_valid r hr with ⟨_, _, _, _, harg, harg1, hupper⟩
  have hmon : Real.exp ((saving : ℝ) * Real.log ((m : ℝ) / r.width)) ≤
      Real.exp ((saving : ℝ) * (logBound r : ℝ)) := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (row_log_upper r hr) (by norm_num [saving]))
  have hx : Real.exp ((argument r : ℚ) : ℝ) ≤ (r.upper : ℝ) :=
    exp_le_of_expUpper (argument r) r.upper 8 harg harg1 (by decide) hupper
  exact hmon.trans (by simpa [argument] using hx)
end Pr73ProfileReal
