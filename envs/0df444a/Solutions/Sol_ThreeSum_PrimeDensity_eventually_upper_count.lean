-- Prove2me | solution 1 for ThreeSum.PrimeDensity.eventually_upper_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:44:00.043563+00:00
-- url     : https://prove2.me/submissions/bb611d10-a58c-4ada-9dff-c12d7db1f8eb

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Theorems.Thm_ThreeSum_Parameters_log_two_upper


set_option autoImplicit false
open ThreeSum ThreeSum.PrimeDensity
open Real Filter Finset
open scoped Topology
noncomputable section
namespace ThreeSum.PrimeDensity
theorem _root_.solution :
    ∀ᶠ y : ℕ in atTop, (Nat.primeCounting y : ℝ) ≤ (7 / 4 : ℝ) * ((y : ℝ) / Real.log y) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := (1 / 4 : ℝ)) (by norm_num))
  have hcoef : Real.log 4 + (1 / 4 : ℝ) < 7 / 4 := by
    have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [ThreeSum.Parameters.log_two_upper]
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with y hy hge
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hratio : 0 ≤ (y : ℝ) / Real.log y :=
    div_nonneg (Nat.cast_nonneg y) (Real.log_pos hy1).le
  have hbound : (Nat.primeCounting y : ℝ) ≤
      (Real.log 4 + 1 / 4) * ((y : ℝ) / Real.log y) := by simpa only [Nat.floor_natCast, mul_div_assoc] using hy
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef.le hratio)
end ThreeSum.PrimeDensity
