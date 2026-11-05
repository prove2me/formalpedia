-- Prove2me | solution 1 for Pr73ProfileReal.real_characteristic_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/3e4d611b-16f3-436f-9c63-b874a66c560a

import Definitions.Def_Pr73ProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Pr73ProfileReal
import Theorems.Thm_Pr73ProfileReal_row_exp_upper
import Theorems.Thm_Pr73ProfileCertificate_rational_upper_lt_one


set_option autoImplicit true
open Pr73ProfileReal
open AnalyticEnclosures Pr73ProfileCertificate
namespace Pr73ProfileReal
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
end Pr73ProfileReal
