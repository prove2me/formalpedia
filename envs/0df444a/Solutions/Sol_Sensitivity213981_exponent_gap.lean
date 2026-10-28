-- Prove2me | solution 1 for Sensitivity213981.exponent_gap
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T18:30:06.453087+00:00
-- url     : https://prove2.me/submissions/ee0cb3a7-fe29-4fda-9bcf-b48d5f2849bc

/- Exact exponent comparison for the sensitivity campaign; no Boolean seed is assumed here. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace Sensitivity213981Arithmetic

theorem integer_comparison :
    (5591^4 : Nat)^100000 > 10121928^213981 := by decide +kernel

theorem exponent_lt_of_power_comparison (g r p q : ℕ) (hr : 1 < r)
    (hq : 0 < q) (hpow : r^p < g^q) :
    (p : ℝ) / q < Real.log (g : ℝ) / Real.log (r : ℝ) := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hrp : (0 : ℝ) < r := by linarith
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hcast : (r : ℝ)^p < (g : ℝ)^q := by exact_mod_cast hpow
  have hlog := Real.log_lt_log (pow_pos hrp p) hcast
  rw [Real.log_pow, Real.log_pow] at hlog
  apply (lt_div_iff₀ (Real.log_pos hr1)).2
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hqp).2
  nlinarith


end Sensitivity213981Arithmetic

theorem solution :
    (213981 : ℝ) / 100000 < 4 * Real.log 5591 / Real.log 10121928 := by
  have h := Sensitivity213981Arithmetic.exponent_lt_of_power_comparison
    (5591^4) 10121928 213981 100000 (by norm_num) (by norm_num)
    Sensitivity213981Arithmetic.integer_comparison
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h

#print axioms solution
