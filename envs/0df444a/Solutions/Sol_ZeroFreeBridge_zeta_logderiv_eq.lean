-- Prove2me | solution 1 for ZeroFreeBridge.zeta_logderiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:54:25.981719+00:00
-- url     : https://prove2.me/submissions/8f0b406e-5503-4259-8cc9-8977e4cba345

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib

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








theorem solution {s : ℂ} (hs : s ≠ 1) (hz1 : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s
      = -(s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s := by
  have hsne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hEq : riemannZeta =ᶠ[nhds s] (fun w => (w - 1)⁻¹ * riemannZeta₁ w) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with w hw; exact riemannZeta_eq_inv_sub_mul hw
  have h1 : HasDerivAt (fun w : ℂ => (w - 1)⁻¹) (-1 / (s - 1) ^ 2) s := by
    have hb : HasDerivAt (fun w : ℂ => w - 1) 1 s := (hasDerivAt_id s).sub_const 1
    exact hb.inv hsne
  have h2 : HasDerivAt riemannZeta₁ (deriv riemannZeta₁ s) s :=
    (differentiable_riemannZeta₁ s).hasDerivAt
  have hprod := (h1.mul h2).congr_of_eventuallyEq hEq
  rw [hprod.deriv, riemannZeta_eq_inv_sub_mul hs]
  field_simp
