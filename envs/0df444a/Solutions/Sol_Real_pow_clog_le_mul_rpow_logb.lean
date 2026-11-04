-- Prove2me | solution 1 for Real.pow_clog_le_mul_rpow_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:50.265108+00:00
-- url     : https://prove2.me/submissions/312381dd-52b4-4dfc-bc88-c2a6bf91062d

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Theorems.Thm_Real_natCast_clog_lt_logb_add_one

set_option autoImplicit false
section
open Real
namespace Real
theorem _root_.solution (b : ℕ) {n : ℕ} {c : ℝ} (hn : 1 ≤ n) (hc : 1 ≤ c) :
    c ^ Nat.clog b n ≤ c * (n : ℝ) ^ logb b c := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hswap : c ^ logb b n = (n : ℝ) ^ logb b c := by
    rw [rpow_def_of_pos hc0, rpow_def_of_pos (Nat.cast_pos.2 hn), logb, logb]
    ring_nf
  calc c ^ Nat.clog b n = c ^ (Nat.clog b n : ℝ) := (rpow_natCast c _).symm
    _ ≤ c ^ (logb b n + 1) :=
        rpow_le_rpow_of_exponent_le hc (natCast_clog_lt_logb_add_one b n).le
    _ = c * (n : ℝ) ^ logb b c := by rw [rpow_add_one hc0.ne', hswap, mul_comm]
end Real
