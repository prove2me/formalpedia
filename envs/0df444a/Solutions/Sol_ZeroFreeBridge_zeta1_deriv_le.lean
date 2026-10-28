-- Prove2me | solution 1 for ZeroFreeBridge.zeta1_deriv_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:59:32.936962+00:00
-- url     : https://prove2.me/submissions/9524858d-2c96-40d0-aa76-54df365890ca

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_zeta1_norm_le

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




theorem solution {w : ℂ} (hw : w ∈ closedBall (1 : ℂ) (1/4)) :
    ‖deriv riemannZeta₁ w‖ ≤ 12 := by
  have hd : DiffContOnCl ℂ riemannZeta₁ (ball w (1/4)) :=
    ⟨differentiable_riemannZeta₁.differentiableOn, differentiable_riemannZeta₁.continuous.continuousOn⟩
  have hb : ∀ z ∈ sphere w (1/4), ‖riemannZeta₁ z‖ ≤ 3 := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    rw [mem_closedBall, Complex.dist_eq] at hw
    refine zeta1_norm_le ?_
    rw [mem_closedBall, Complex.dist_eq]
    calc ‖z - 1‖ = ‖(z - w) + (w - 1)‖ := by congr 1; ring
      _ ≤ ‖z - w‖ + ‖w - 1‖ := norm_add_le _ _
      _ ≤ 1/4 + 1/4 := by rw [hz]; linarith
      _ = 1/2 := by norm_num
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/4) hd hb
  linarith
