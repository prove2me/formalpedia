-- Prove2me | solution 1 for ZeroFreeBridge.htwo_shape_of_bc_sum
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:55:20.152204+00:00
-- url     : https://prove2.me/submissions/53647f40-e3af-4d9a-a2e9-afb25e3bd47a

import Mathlib
import Theorems.Thm_ZeroFreeBridge_weighted_sum_re_nonneg
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

namespace ZeroFreeBridge





/-- **`htwo` glue.**  BC-SUM + weighted Herglotz nonnegativity ⟹ `-Re(ζ'/ζ)(z) ≤ AL`. -/
theorem htwo_of_blaschke {f : ℂ → ℂ} (s : Finset ℂ) (m : ℂ → ℤ) (z : ℂ) (AL : ℝ)
    (hbc : (-(logDeriv f z)).re ≤ AL - (∑ ρ ∈ s, (m ρ : ℂ) / (z - ρ)).re)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ) (hlt : ∀ ρ ∈ s, ρ.re < z.re) :
    (-(logDeriv f z)).re ≤ AL := by
  have hnn := weighted_sum_re_nonneg s m z hm hlt
  linarith

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, the divisor-TRANSLATION lemma — item 3 core): `divisor` commutes with a
   constant shift.  `bc_sum_blaschke` is centred at `0`, so ζ enters as `f = ζ(c₀+·)` and its divisor is
   `divisor (ζ(c₀+·)) (ball 0 R)`; the Herglotz-sum reindexing needs this to be `divisor ζ (ball c₀ R)`
   evaluated at the shifted point.

   `divisor f U z = (meromorphicOrderAt f z).untop₀` (`divisor_apply`), and the meromorphic order is
   invariant under a translation `g = (c₀+·)` because `deriv g = 1 ≠ 0`
   (`meromorphicOrderAt_comp_of_deriv_ne_zero`).  Hence

     `divisor (fun w => f (c₀+w)) U' u = divisor f U (c₀+u)`

   whenever both sides are in-domain and `f` is meromorphic on `U`.  This is the last uncertain-API
   piece of the ζ instantiation, and it is a direct consequence of the Mathlib order-composition API.
   conjecture1_proved = False (NOT a proof of RH).
-/


open Complex MeromorphicOn

namespace ZeroFreeBridge

/-- **Divisor under a constant shift.**  `divisor (fun w => f (c₀+w)) U' u = divisor f U (c₀+u)`. -/
theorem divisor_comp_const_add_apply {f : ℂ → ℂ} {U U' : Set ℂ} (c₀ : ℂ)
    (hf : MeromorphicOn f U) (hf' : MeromorphicOn (fun w => f (c₀ + w)) U')
    {u : ℂ} (hu' : u ∈ U') (hu : c₀ + u ∈ U) :
    divisor (fun w => f (c₀ + w)) U' u = divisor f U (c₀ + u) := by
  rw [divisor_apply hf' hu', divisor_apply hf hu]
  congr 1
  have hg : AnalyticAt ℂ (fun w => c₀ + w) u := by fun_prop
  have hg' : deriv (fun w => c₀ + w) u ≠ 0 := by
    rw [deriv_const_add']; simp
  have hcomp : (fun w => f (c₀ + w)) = f ∘ (fun w => c₀ + w) := rfl
  rw [hcomp, meromorphicOrderAt_comp_of_deriv_ne_zero hg hg']

/-- **Herglotz-sum reindexing.**  The recentred Herglotz sum (over the recentred zero set `s`) equals
    the original-coordinate sum (over `s.image (c₀+·)`, the true zeros): the divisor translates and
    `(c₀+z) - (c₀+u) = z - u`.  This turns `bc_sum_blaschke`'s output sum into the form
    `hzero_of_blaschke` / `herglotz_re_ge` consume. -/
theorem herglotz_sum_reindex {f : ℂ → ℂ} {U U' : Set ℂ} (c₀ z : ℂ)
    (hf : MeromorphicOn f U) (hf' : MeromorphicOn (fun w => f (c₀ + w)) U')
    (s : Finset ℂ) (hs_dom : ∀ u ∈ s, u ∈ U' ∧ c₀ + u ∈ U) :
    (∑ u ∈ s, (divisor (fun w => f (c₀ + w)) U' u : ℂ) / (z - u))
      = ∑ ρ ∈ s.image (fun u => c₀ + u), (divisor f U ρ : ℂ) / ((c₀ + z) - ρ) := by
  rw [Finset.sum_image (fun x _ y _ h => add_left_cancel h)]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  obtain ⟨hu', hu_dom⟩ := hs_dom u hu
  rw [divisor_comp_const_add_apply c₀ hf hf' hu' hu_dom]
  congr 1
  ring

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, entire-part PLUMBING): the two mechanical lemmas that connect the
   interior-point bound (`DlvpBCDerivInterior`) to the Blaschke BC-SUM (`bc_sum_blaschke`).

   (a) `norm_logDeriv_le_of_sphere_log_norm_le_interior` — the interior entire-part bound driven by a
       SPHERE oscillation bound (not the whole ball): `log‖g‖ = Re(log g)` is harmonic, so a boundary
       bound propagates to the disk by maximum modulus (`DlvpMaxMod.norm_le_on_ball_of_sphere`, via
       `exp`), and the resulting ball bound feeds `norm_logDeriv_le_of_log_norm_le_interior`.  This is
       exactly the shape available for ζ's Blaschke `g`, whose boundary `log‖g‖` equals `log‖ζ‖`
       (Blaschke factors have modulus 1 on the sphere).

   (b) `logDeriv_comp_const_add` — the RECENTRING: `bc_sum_blaschke` lives on `ball 0 R`, so ζ enters as
       `f(w) = ζ(c + w)`; its log-derivative is ζ's, shifted: `logDeriv (fun w => ζ(c+w)) z =
       logDeriv ζ (c+z)` (chain rule, `deriv (c+·) = 1`).

   conjecture1_proved = False (NOT a proof of RH).
-/



open Complex Metric

namespace ZeroFreeBridge



/-- **(b) Recentring the log-derivative.**  `logDeriv (fun w => f (c + w)) z = logDeriv f (c + z)`
    (chain rule; `deriv (c + ·) = 1`).  Sends ζ's log-derivative into `bc_sum_blaschke`'s `ball 0 R`
    coordinates. -/
theorem logDeriv_comp_const_add (f : ℂ → ℂ) (c z : ℂ) (hf : DifferentiableAt ℂ f (c + z)) :
    logDeriv (fun w => f (c + w)) z = logDeriv f (c + z) := by
  have hg : DifferentiableAt ℂ (fun w => c + w) z := by fun_prop
  have := logDeriv_comp hf hg
  simp only [Function.comp_def] at this
  rw [this]
  simp

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, the LHS recentring bridge): connect `bc_sum_blaschke`'s output form
   `(-(logDeriv f z)).re` (with `f = ζ(c₀+·)` the recentred ζ) to the `(-deriv ζ w / ζ w).re` form that
   the region skeleton (`DlvpPole.dlvp_region_of_bc_inputs`, `DlvpZetaRegion.dlvp_zeta_region`) consumes.

   `logDeriv (fun w => ζ(c₀+w)) z = logDeriv ζ (c₀+z)` (`DlvpEntirePlumbing.logDeriv_comp_const_add`), and
   `logDeriv ζ w = deriv ζ w / ζ w` by definition, with `-(a/b) = -a/b`.  So the recentred BC-SUM's
   left-hand side is exactly the skeleton's.  This is the last piece of connective tissue between the
   Blaschke BC-SUM and the region skeleton (the remaining work is the Herglotz-sum reindexing, whose
   VALUE is recentring-invariant since `(z-c₀)-(ρ-c₀) = z-ρ`).  conjecture1_proved = False (NOT RH).
-/


open Complex

namespace ZeroFreeBridge

/-- **LHS recentring.**  The recentred log-derivative real part equals the skeleton's `-Re(ζ'/ζ)` at the
    shifted point: `(-(logDeriv (fun w => ζ(c₀+w)) z)).re = (-deriv ζ (c₀+z) / ζ (c₀+z)).re`. -/
theorem neg_logDeriv_zeta_recenter_re (c₀ z : ℂ)
    (hf : DifferentiableAt ℂ riemannZeta (c₀ + z)) :
    (-(logDeriv (fun w => riemannZeta (c₀ + w)) z)).re
      = (-deriv riemannZeta (c₀ + z) / riemannZeta (c₀ + z)).re := by
  rw [logDeriv_comp_const_add riemannZeta c₀ z hf]
  simp only [logDeriv, Pi.div_apply, neg_div]

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, the downstream BRIDGE): turn `bc_sum_blaschke`'s recentred output into the
   region skeleton's `hzero` input, entirely by composition of already-built lemmas.

   `bc_sum_blaschke` gives (for `f = ζ(c₀+·)`, recentred eval point `zr = (σ+γI) - c₀`)
     `-Re(logDeriv f zr) ≤ AL - Re(Σ_u divisor f (ball 0 R) u /(zr - u))`.
   `herglotz_sum_reindex` rewrites the sum to the ORIGINAL-coordinate Herglotz sum
     `Σ_ρ divisor ζ (ball c₀ R) ρ /((σ+γI) - ρ)`; `neg_logDeriv_zeta_recenter_re` rewrites the left side
   to `-deriv ζ (σ+γI)/ζ(σ+γI)`; `hzero_of_blaschke` (the Herglotz lower bound) then delivers the
   `hzero` shape `-Re(ζ'/ζ)(σ+γI) ≤ AL - k/(σ-β)` that `DlvpZetaRegion.dlvp_zeta_region` consumes.

   conjecture1_proved = False (NOT a proof of RH).
-/





open Complex MeromorphicOn

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge




theorem solution (c₀ : ℂ) (σ γ AL : ℝ) (R : ℝ)
    (hf_mero : MeromorphicOn riemannZeta (Metric.ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R))
    (s_rec : Finset ℂ)
    (hs_dom : ∀ u ∈ s_rec, u ∈ Metric.ball (0 : ℂ) R ∧ c₀ + u ∈ Metric.ball c₀ R)
    (hcz : c₀ + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀) = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
    (hdiff : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I))
    (hbc : (-(logDeriv (fun w => riemannZeta (c₀ + w))
                ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀))).re
             ≤ AL - (∑ u ∈ s_rec,
                 (divisor (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R) u : ℂ)
                   / (((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀) - u)).re)
    (hm : ∀ ρ ∈ s_rec.image (fun u => c₀ + u), 0 ≤ divisor riemannZeta (Metric.ball c₀ R) ρ)
    (hlt : ∀ ρ ∈ s_rec.image (fun u => c₀ + u), ρ.re < σ) :
    (-deriv riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
        / riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)).re ≤ AL := by
  rw [herglotz_sum_reindex c₀ ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀) hf_mero hf'_mero s_rec hs_dom,
    hcz] at hbc
  rw [neg_logDeriv_zeta_recenter_re c₀ ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀)
      (by rw [hcz]; exact hdiff), hcz] at hbc
  have hkey := htwo_of_blaschke (f := riemannZeta) (s_rec.image (fun u => c₀ + u))
    (fun ρ => divisor riemannZeta (Metric.ball c₀ R) ρ) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) AL
    (by simpa only [logDeriv, Pi.div_apply, neg_div] using hbc)
    hm (by
      intro ρ hρ
      have := hlt ρ hρ
      simpa using this)
  simpa only [logDeriv, Pi.div_apply, neg_div] using hkey
