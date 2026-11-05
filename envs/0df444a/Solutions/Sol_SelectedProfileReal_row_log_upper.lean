-- Prove2me | solution 1 for SelectedProfileReal.row_log_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/f611a929-3c2a-4d31-a0c9-f4731abfe705

import Definitions.Def_SelectedProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_SelectedProfileReal
import Theorems.Thm_SelectedProfileReal_row_valid
import Theorems.Thm_SelectedProfileReal_log_two_upper
import Theorems.Thm_AnalyticEnclosures_log_le_of_expPoly
import Theorems.Thm_AnalyticEnclosures_log_scale_upper


set_option autoImplicit true
open SelectedProfileReal
open AnalyticEnclosures SelectedProfileCertificate
namespace SelectedProfileReal
theorem _root_.solution (r : Row) (hr : r ∈ rows) :
    Real.log ((m : ℝ) / r.width) ≤ (logBound r : ℝ) := by
  rcases row_valid r hr with ⟨hw, _, hL, hpoly, _, _, _⟩
  have hwr : (0 : ℝ) < r.width := by exact_mod_cast hw
  have hratio : (0 : ℚ) < ratio r := by
    unfold ratio
    have hwidth : (0 : ℚ) < r.width := by exact_mod_cast hw
    norm_num [m]
    positivity
  have hlog := log_le_of_expPoly (ratio r) r.logSmall 24 hratio hL hpoly
  have heq : (m : ℝ) / r.width = (2 : ℝ) ^ r.scale * (ratio r : ℝ) := by
    simp only [ratio, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
    field_simp
  have h := log_scale_upper ((m : ℝ) / r.width) (ratio r : ℝ)
    (r.logSmall : ℝ) (logTwoUpper : ℝ) r.scale (by exact_mod_cast hratio)
    heq hlog log_two_upper
  simpa [logBound] using h
end SelectedProfileReal
