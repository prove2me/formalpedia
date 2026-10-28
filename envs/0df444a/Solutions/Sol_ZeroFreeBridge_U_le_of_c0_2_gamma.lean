-- Prove2me | solution 1 for ZeroFreeBridge.U_le_of_c0_2_gamma
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:43:39.020896+00:00
-- url     : https://prove2.me/submissions/af4d9396-ed5a-4ca5-a777-e514c47837b4

import Mathlib

/- PHASE 4 (dVP frontier, item 2(ii) — Bg = O(L) via Aζ'' = O(log|γ|)): the sphere-oscillation
   constant `Aζ''` for the concrete centre `c₀ = 2+iγ` is O(log|γ|), so the entire-part bound
   `Bg = 4·Aζ''·(R+‖z₀‖)/(R-‖z₀‖)²` (`norm_logDeriv_g_le_wired`) is O(L), `L = log|γ|` — the second
   O(L) input `hAL_concrete` consumes (`hBg`).

   Crux: `U'' = (‖c₀‖+R)/(|γ|-R) + (‖c₀‖+R)/(2-R) = O(|γ|)` (the 2nd term (‖c₀‖+R)/(2-R) dominates,
   since c₀.re=2 and R<3/2 ⟹ 2-R>1/2).  `U_le_of_c0_2_gamma`: `U'' ≤ 2|γ|+11` (‖c₀‖≤2+|γ| via
   `norm_add_le`; first term ≤ 7/2, second ≤ 2|γ|+15/2, by `div_le_iff₀` + `nlinarith`).
   `Azeta_le_of_c0_2_gamma`: `Aζ'' = log U'' - log(2-π²/6) ≤ log((2|γ|+11)/(2-π²/6))` (log monotone
   on the U'' bound + `Real.log_div`).  conjecture1_proved = False (NOT a proof of RH).
-/

open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution (γ R : ℝ) (hR : 0 < R) (hR2 : R < 3/2) (hγ : R + 2 ≤ |γ|) :
    (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (|((2 : ℂ) + (γ : ℂ) * I).im| - R)
      + (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (((2 : ℂ) + (γ : ℂ) * I).re - R)
      ≤ 2 * |γ| + 11 := by
  have hc0re : ((2 : ℂ) + (γ : ℂ) * I).re = 2 := by simp
  have hc0im : |((2 : ℂ) + (γ : ℂ) * I).im| = |γ| := by simp
  have hnorm : ‖(2 : ℂ) + (γ : ℂ) * I‖ ≤ 2 + |γ| := by
    calc ‖(2 : ℂ) + (γ : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(γ : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |γ| := by
          rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            show ‖(2 : ℂ)‖ = 2 by simp]
  rw [hc0re, hc0im]
  have hd1 : (0 : ℝ) < |γ| - R := by linarith
  have hd2 : (0 : ℝ) < 2 - R := by linarith
  have hnn : (0 : ℝ) ≤ ‖(2 : ℂ) + (γ : ℂ) * I‖ := norm_nonneg _
  -- first term ≤ 7/2
  have hfirst : (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (|γ| - R) ≤ 7 / 2 := by
    rw [div_le_iff₀ hd1]; nlinarith [hnorm, hγ, hR2]
  -- second term ≤ 2|γ| + 15/2
  have hsecond : (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (2 - R) ≤ 2 * |γ| + 15 / 2 := by
    rw [div_le_iff₀ hd2]; nlinarith [hnorm, hR2, abs_nonneg γ]
  linarith [hfirst, hsecond]
