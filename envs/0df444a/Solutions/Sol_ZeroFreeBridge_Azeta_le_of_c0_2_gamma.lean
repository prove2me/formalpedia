-- Prove2me | solution 1 for ZeroFreeBridge.Azeta_le_of_c0_2_gamma
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:52:43.817544+00:00
-- url     : https://prove2.me/submissions/c7bec109-4255-4b9b-824d-c2ada9d5f77c

import Mathlib
import Theorems.Thm_ZeroFreeBridge_U_le_of_c0_2_gamma
/- PHASE 4 (dVP frontier, ζ boundary growth — LOWER BOUND): a uniform lower bound on |ζ|
   at Re s = 2, the missing lower half of the ζ-growth sphere input.

   The composition `DlvpBoundaryDecomp.norm_logDeriv_le_of_boundary_split` needs, on the sphere,
   `log‖ζ z‖ - log‖ζ c‖ ≤ Aζ`; the upper half is `zeta_sphere_bound`, the lower half is a POSITIVE
   lower bound `‖ζ c‖ ≥ c₀`.  Centering the dVP disk at `Re c = 2` makes this an absolute constant:

     `2 - π²/6 ≤ ‖ζ(s)‖`   for   `2 ≤ Re s`   (and `2 - π²/6 > 0`).

   Proof: `ζ(s) = ∑ₙ 1/(n+1)^s = 1 + T` (Dirichlet series, `n=0` term is `1`); reverse triangle
   `‖ζ‖ ≥ 1 - ‖T‖`; `‖T‖ ≤ ∑ₙ 1/(n+2)^{Re s} ≤ ∑ₙ 1/(n+2)² = π²/6 - 1` (termwise since `Re s ≥ 2`,
   the tail of Basel `hasSum_zeta_two`); so `‖ζ‖ ≥ 1 - (π²/6 - 1) = 2 - π²/6`.  conjecture1_proved = False.
-/


open Complex

namespace ZeroFreeBridge





/-- The constant is positive: `0 < 2 - π²/6`  (since `π < 3.15 ⟹ π² < 9.93 < 12`). -/
theorem two_sub_pi_sq_div_six_pos : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := by
  nlinarith [Real.pi_lt_d2, Real.pi_pos]



end ZeroFreeBridge


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
    Real.log ((‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (|((2 : ℂ) + (γ : ℂ) * I).im| - R)
        + (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (((2 : ℂ) + (γ : ℂ) * I).re - R))
      - Real.log (2 - Real.pi ^ 2 / 6)
      ≤ Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) := by
  have hc0re : ((2 : ℂ) + (γ : ℂ) * I).re = 2 := by simp
  have hc0im : |((2 : ℂ) + (γ : ℂ) * I).im| = |γ| := by simp
  have hd1 : (0 : ℝ) < |γ| - R := by linarith
  have hd2 : (0 : ℝ) < 2 - R := by linarith
  have hnn : (0 : ℝ) ≤ ‖(2 : ℂ) + (γ : ℂ) * I‖ := norm_nonneg _
  -- U'' > 0
  have hUpos : (0 : ℝ) < (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (|((2 : ℂ) + (γ : ℂ) * I).im| - R)
      + (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (((2 : ℂ) + (γ : ℂ) * I).re - R) := by
    rw [hc0re, hc0im]
    have h1 : (0 : ℝ) < (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (|γ| - R) := by positivity
    have h2 : (0 : ℝ) < (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (2 - R) := by positivity
    linarith
  have hpi : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := two_sub_pi_sq_div_six_pos
  have hlogU : Real.log ((‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (|((2 : ℂ) + (γ : ℂ) * I).im| - R)
        + (‖(2 : ℂ) + (γ : ℂ) * I‖ + R) / (((2 : ℂ) + (γ : ℂ) * I).re - R))
      ≤ Real.log (2 * |γ| + 11) :=
    Real.log_le_log hUpos (U_le_of_c0_2_gamma γ R hR hR2 hγ)
  rw [Real.log_div (by positivity) (ne_of_gt hpi)]
  linarith [hlogU]
