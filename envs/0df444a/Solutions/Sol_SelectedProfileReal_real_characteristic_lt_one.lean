-- Prove2me | solution 1 for SelectedProfileReal.real_characteristic_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/58e5b6de-70ed-4aa2-b465-06d0f7f2815b

import Definitions.Def_SelectedProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_SelectedProfileReal
import Theorems.Thm_SelectedProfileReal_row_exp_upper
import Theorems.Thm_SelectedProfileCertificate_rational_upper_lt_one


set_option autoImplicit true
open SelectedProfileReal
open AnalyticEnclosures SelectedProfileCertificate
namespace SelectedProfileReal
theorem _root_.solution : exponentialCharacteristic < 1 := by
  have hrow : ∀ r ∈ rows,
      (weight r : ℝ) * Real.exp ((saving : ℝ) * Real.log ((m : ℝ) / r.width)) ≤
        ((weight r * r.upper : ℚ) : ℝ) := by
    intro r hr
    have hweight : (0 : ℝ) ≤ (weight r : ℝ) := by
      simp only [weight, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
      positivity
    simpa using mul_le_mul_of_nonneg_left (row_exp_upper r hr) hweight
  have hsum := List.sum_le_sum hrow
  have hcast : (rows.map (fun r => ((weight r * r.upper : ℚ) : ℝ))).sum =
      (rationalUpper : ℝ) := by
    simp [rationalUpper, Function.comp_def]
  unfold exponentialCharacteristic
  rw [hcast] at hsum
  exact hsum.trans_lt (by exact_mod_cast rational_upper_lt_one)
end SelectedProfileReal
