-- Prove2me | solution 1 for Sensitivity213303.exponent_gap
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T18:28:51.117535+00:00
-- url     : https://prove2.me/submissions/3346cf55-ba66-4ed3-9aed-2b64c01b0cac

/- Exact exponent comparison for the sensitivity campaign; no Boolean seed is assumed here. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace Sensitivity213303Arithmetic

theorem integer_comparison :
    (10007^4 : Nat)^100000 > 31739938^213303 := by decide +kernel

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


end Sensitivity213303Arithmetic

theorem solution :
    (213303 : ℝ) / 100000 < 4 * Real.log 10007 / Real.log 31739938 := by
  have h := Sensitivity213303Arithmetic.exponent_lt_of_power_comparison
    (10007^4) 31739938 213303 100000 (by norm_num) (by norm_num)
    Sensitivity213303Arithmetic.integer_comparison
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h

#print axioms solution
