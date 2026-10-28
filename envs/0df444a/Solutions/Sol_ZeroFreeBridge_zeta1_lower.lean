-- Prove2me | solution 1 for ZeroFreeBridge.zeta1_lower
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:02:12.751993+00:00
-- url     : https://prove2.me/submissions/7835bb6a-a918-4578-81f1-1ab761203a1b

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_zeta1_deriv_le

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






theorem solution {σ : ℝ} (h1 : 1 ≤ σ) (h2 : σ - 1 ≤ 1/48) :
    3/4 ≤ ‖riemannZeta₁ (σ : ℂ)‖ := by
  have hmem : (σ : ℂ) ∈ closedBall (1 : ℂ) (1/4) := by
    rw [mem_closedBall, Complex.dist_eq,
      show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hmvt : ‖riemannZeta₁ (σ : ℂ) - riemannZeta₁ 1‖ ≤ 12 * ‖(σ : ℂ) - 1‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => differentiable_riemannZeta₁ x)
      (fun x hx => zeta1_deriv_le hx) (convex_closedBall 1 (1/4)) (by simp) hmem
  rw [riemannZeta₁_one] at hmvt
  have hnorm : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hnorm] at hmvt
  have hrev := norm_sub_norm_le (1 : ℂ) (riemannZeta₁ (σ : ℂ))
  rw [norm_one, norm_sub_rev] at hrev
  linarith [hrev, hmvt, h2]
