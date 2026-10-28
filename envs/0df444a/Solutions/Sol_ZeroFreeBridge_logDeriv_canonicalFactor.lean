-- Prove2me | solution 1 for ZeroFreeBridge.logDeriv_canonicalFactor
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:44:54.781955+00:00
-- url     : https://prove2.me/submissions/c9992aff-e4f3-4ebe-9e55-84e50b42f407

import Mathlib

/- PHASE 4 (dVP frontier, BLASCHKE item (d) FOUNDATION): the log-derivative of the canonical factor.

   Item (d) revises the obligation-(i) Herglotz sum from the monomial `1/(z-ρ)` to the canonical
   (Blaschke) factor.  `canonicalFactor R w z = (R² - conj w · z)/(R(z-w))` is a ratio of affine
   functions, so its log-derivative is the difference of the two affine log-derivatives:

     `logDeriv (canonicalFactor R w) z = -conj w/(R² - conj w · z) - 1/(z-w)`.

   The `-1/(z-w)` term is exactly the monomial Herglotz contribution (with sign fixed by the
   `-divisor` exponent in the Blaschke product); the extra `-conj w/(R² - conj w · z)` term is the
   BOUNDED correction (its pole `R²/conj w` lies OUTSIDE the disk), which gets absorbed into the
   O(L) entire-part bound.  Function-agnostic.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {R : ℝ} {w z : ℂ} (hR : R ≠ 0)
    (hnum : (R : ℂ) ^ 2 - (starRingEnd ℂ) w * z ≠ 0) (hzw : z - w ≠ 0) :
    logDeriv (canonicalFactor R w) z
      = -(starRingEnd ℂ) w / ((R : ℂ) ^ 2 - (starRingEnd ℂ) w * z) - 1 / (z - w) := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hden_ne : (R : ℂ) * (z - w) ≠ 0 := mul_ne_zero hRc hzw
  -- derivative VALUES of the two affine pieces (no HasDerivAt annotation ⟹ no module diamond).
  have d1 : deriv (fun z : ℂ => (R : ℂ) ^ 2 - (starRingEnd ℂ) w * z) z = -(starRingEnd ℂ) w := by
    simp
  have d2 : deriv (fun z : ℂ => (R : ℂ) * (z - w)) z = (R : ℂ) := by
    simp
  rw [canonicalFactor_def, logDeriv_div z hnum hden_ne (by fun_prop) (by fun_prop),
    logDeriv_apply, logDeriv_apply, d1, d2]
  have hsimp : (R : ℂ) / ((R : ℂ) * (z - w)) = 1 / (z - w) := by
    rw [mul_comm]; field_simp
  rw [hsimp]
