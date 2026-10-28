-- Prove2me | solution 1 for ZeroFreeBridge.weighted_sum_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:47:32.411271+00:00
-- url     : https://prove2.me/submissions/86b1979a-7dc3-4757-9871-d3d4de8d4824

import Mathlib

/- PHASE 4 (dVP frontier, Blaschke → skeleton GLUE): combine the Blaschke BC-SUM with the Herglotz
   lower bound to produce the reduction skeleton's `hzero` / `htwo` shapes.

   `DlvpBCSumBlaschke.bc_sum_blaschke` gives `-Re(ζ'/ζ)(z) ≤ AL - Re(Z)`, `Z = Σ_ρ (m ρ)/(z-ρ)`.
   `DlvpHerglotzLower.herglotz_re_ge` gives `Re(Z) ≥ k/(σ-β)` (keep the equal-height zero, drop the
   rest).  A `linarith` combines them into `-Re(ζ'/ζ)(z) ≤ AL - k/(σ-β)` — the exact `hzero` input of
   `DlvpPole.dlvp_region_of_bc_inputs`.  Dropping ALL zeros (`Re(Z) ≥ 0`, `weighted_sum_re_nonneg`)
   instead gives the `htwo` shape `-Re(ζ'/ζ)(z) ≤ AL`.  Abstract in the function `f` (composes with the
   ζ recentering).  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution (s : Finset ℂ) (m : ℂ → ℤ) (z : ℂ)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ) (hlt : ∀ ρ ∈ s, ρ.re < z.re) :
    0 ≤ (∑ ρ ∈ s, (m ρ : ℂ) / (z - ρ)).re := by
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro ρ hρ
  have hzr : 0 < (z - ρ).re := by rw [Complex.sub_re]; linarith [hlt ρ hρ]
  have hre : ((m ρ : ℂ) / (z - ρ)).re = (m ρ : ℝ) * ((z - ρ)⁻¹).re := by
    rw [div_eq_mul_inv, Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
    ring
  rw [hre]
  apply mul_nonneg (by exact_mod_cast hm ρ hρ)
  rw [Complex.inv_re]
  exact div_nonneg hzr.le (Complex.normSq_nonneg _)
