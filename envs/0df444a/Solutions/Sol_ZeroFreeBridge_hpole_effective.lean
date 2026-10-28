-- Prove2me | solution 1 for ZeroFreeBridge.hpole_effective
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:04:03.250458+00:00
-- url     : https://prove2.me/submissions/95e163aa-061d-4eaa-bddc-d14177d7e512

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_zeta1_deriv_le
import Theorems.Thm_ZeroFreeBridge_zeta1_lower
import Theorems.Thm_ZeroFreeBridge_zeta_logderiv_eq

/- PHASE 4 (dVP frontier, the EFFECTIVE pole bound): replace Mathlib's non-effective pole constant
   (`log_deriv_riemannZeta_add_inv_sub_bounded`, a bare `∃`) with an EXPLICIT one.

   The only non-effective input to `dlvp_zeta_region_rate`'s constant `c` is the pole bound
   `Re(-ζ'/ζ(σ)) ≤ Re(1/(σ-1)) + A₀` near `σ = 1`.  This file makes it explicit with
   `A₀ = 16`, `ε₀ = 1/48`, via a Cauchy estimate on `ζ₁ := (·-1)·ζ` (Mathlib `riemannZeta₁`,
   entire, `ζ₁ 1 = 1`, `ζ = (s-1)⁻¹·ζ₁`):

     * `zeta1_norm_le`   `‖ζ₁ z‖ ≤ 3` on `closedBall 1 (1/2)` — via the explicit `zeta_strip_bound`;
     * `zeta1_deriv_le`  `‖ζ₁' w‖ ≤ 12` on `closedBall 1 (1/4)` — Cauchy estimate (radius 1/4);
     * `zeta1_lower`     `‖ζ₁ σ‖ ≥ 3/4` for `σ-1 ≤ 1/48` — mean-value bound `‖ζ₁ σ - 1‖ ≤ 12(σ-1)`;
     * `zeta_logderiv_eq`  `ζ'/ζ = -(s-1)⁻¹ + ζ₁'/ζ₁` at an explicit point (`s≠1`, `ζ₁ s≠0`);
     * `hpole_effective`   `Re(-ζ'/ζ(σ)) ≤ Re(1/(σ-1)) + 16` for `1 < σ`, `σ-1 < 1/48`
       (`|ζ₁'/ζ₁| ≤ 12/(3/4) = 16`).

   Feeding this into the rate construction makes `c = 1/(112·(16 + 48 + E))` a CONCRETE positive
   real (`E` the explicit constant from `dlvp_zeta_region_rate`).  The dVP constant is now effective.
   conjecture1_proved = False (NOT a proof of RH).
-/



open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge










theorem solution {σ : ℝ} (h1 : 1 < σ) (h2 : σ - 1 < 1/48) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ (1 / ((σ : ℂ) - 1)).re + 16 := by
  have hσne : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hlow : 3/4 ≤ ‖riemannZeta₁ (σ : ℂ)‖ := zeta1_lower (le_of_lt h1) (le_of_lt h2)
  have hz1ne : riemannZeta₁ (σ : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow; linarith
  have heq := zeta_logderiv_eq hσne hz1ne
  have hmem : (σ : ℂ) ∈ closedBall (1 : ℂ) (1/4) := by
    rw [mem_closedBall, Complex.dist_eq,
      show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hderivbd : ‖deriv riemannZeta₁ (σ : ℂ)‖ ≤ 12 := zeta1_deriv_le hmem
  have hratio : ‖deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ)‖ ≤ 16 := by
    rw [norm_div, div_le_iff₀ (by linarith : (0:ℝ) < ‖riemannZeta₁ (σ : ℂ)‖)]
    nlinarith [hderivbd, hlow, norm_nonneg (deriv riemannZeta₁ (σ : ℂ))]
  have hre_ge : -16 ≤ (deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ)).re := by
    have h := Complex.abs_re_le_norm (deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ))
    rw [abs_le] at h; linarith [h.1, hratio]
  have hval : (-deriv riemannZeta (σ : ℂ)) / riemannZeta (σ : ℂ)
      = ((σ : ℂ) - 1)⁻¹ - deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ) := by
    rw [neg_div, heq]; ring
  rw [hval, one_div, Complex.sub_re]
  linarith [hre_ge]
