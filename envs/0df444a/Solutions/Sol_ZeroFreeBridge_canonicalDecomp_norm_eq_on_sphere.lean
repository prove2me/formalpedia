-- Prove2me | solution 1 for ZeroFreeBridge.canonicalDecomp_norm_eq_on_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:53:59.335356+00:00
-- url     : https://prove2.me/submissions/c2353171-eb18-43ac-b999-e3e5b09a9d6f

import Mathlib
import Theorems.Thm_ZeroFreeBridge_dense_inter_sphere_of_codiscrete
import Theorems.Thm_ZeroFreeBridge_norm_finprod_canonicalFactor_zpow_eq_one
/- PHASE 4 (dVP frontier, BLASCHKE step 1): the pointwise sphere identity ‖f‖ = ‖g‖ from a
   codiscrete factorization, via continuity + density.

   `MeromorphicOn.exists_canonicalDecomp` gives `f =ᶠ[codiscreteWithin closedBall] B • g` (with
   `B` the finite Blaschke product `∏ᶠ canonicalFactor^{-divisor}`), i.e. `f w = B w • g w` only
   OFF a discrete exceptional set.  On the boundary sphere `‖B‖ = 1`
   (`DlvpBlaschke.norm_finprod_canonicalFactor_zpow_eq_one`), so wherever the factorization holds
   `‖f w‖ = ‖g w‖`.  Both norms are continuous, and the agreement set is dense in the sphere (the
   exceptional set is discrete, hence finite on the compact sphere, hence its complement is
   cofinite = dense).  `Set.EqOn.closure` then upgrades the identity to EVERY sphere point.

   This atom does the continuity+density upgrade, taking density as the one explicit hypothesis
   `hdense` (dischargeable from codiscreteWithin ⟹ locally-finite complement ⟹ finite on the
   compact sphere).  Function-agnostic in `f, g, B`.  conjecture1_proved = False (NOT RH).
-/


open Complex Metric Set

namespace ZeroFreeBridge

/-- **Pointwise sphere identity from a codiscrete unit-modulus factorization.**  If `f w = B w • g w`
    on a set dense in `sphere 0 R`, `‖B‖ = 1` on the sphere, and `f, g` are continuous on the sphere,
    then `‖f z‖ = ‖g z‖` for EVERY `z ∈ sphere 0 R`. -/
theorem norm_eq_of_codiscrete_factor_on_sphere {f g B : ℂ → ℂ} {R : ℝ}
    (hcont_f : ContinuousOn f (sphere 0 R)) (hcont_g : ContinuousOn g (sphere 0 R))
    (hB1 : ∀ z ∈ sphere (0 : ℂ) R, ‖B z‖ = 1)
    (hdense : sphere (0 : ℂ) R ⊆ closure ({w | f w = B w • g w} ∩ sphere 0 R))
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    ‖f z‖ = ‖g z‖ := by
  set S : Set ℂ := {w | f w = B w • g w} ∩ sphere 0 R with hSdef
  have hSsub : S ⊆ sphere (0 : ℂ) R := Set.inter_subset_right
  have hEq : Set.EqOn (fun w => ‖f w‖) (fun w => ‖g w‖) S := by
    intro w hw
    show ‖f w‖ = ‖g w‖
    rw [hw.1, norm_smul, hB1 w hw.2, one_mul]
  exact hEq.of_subset_closure hcont_f.norm hcont_g.norm hSsub hdense hz

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, BLASCHKE step 3a): ‖f‖ = ‖g‖ on the sphere for the canonical
   decomposition — the no-AP boundary identity, assembled for the actual `CanonicalDecomp`.

   Composes the Blaschke atoms:
     * `DlvpBlaschke.norm_finprod_canonicalFactor_zpow_eq_one` — ‖Blaschke product‖ = 1 on the sphere;
     * `DlvpSphereDense.dense_inter_sphere_of_codiscrete` — the codiscrete agreement set is dense in
       the sphere;
     * `DlvpBlaschkeSphere.norm_eq_of_codiscrete_factor_on_sphere` — continuity + density upgrade.

   Result: for a `CanonicalDecomp f g R` with `f, g` continuous on the sphere, `‖f z‖ = ‖g z‖` for
   every `z ∈ sphere 0 R`.  With `f = ζ` this makes the boundary `M' = sup log‖ζ‖ − log‖g c‖ = O(L)`
   with NO zero-factor term.  conjecture1_proved = False (NOT a proof of RH).
-/




open Complex Metric MeromorphicOn Filter

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp f g R)
    (hcont_f : ContinuousOn f (sphere 0 R)) (hcont_g : ContinuousOn g (sphere 0 R))
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    ‖f z‖ = ‖g z‖ := by
  -- support of the (negated) divisor is finite and lives in the open ball.
  have hfin : (Function.support (fun u => -(divisor f (ball 0 R) u))).Finite := by
    simpa [Function.support_neg] using D.meromorphicOn.divisor_ball_support_finite
  have hsupp : ∀ u ∈ hfin.toFinset, u ∈ ball (0 : ℂ) R := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    have hdu : divisor f (ball 0 R) u ≠ 0 := fun h => hu (by rw [h]; ring)
    exact (divisor f (ball 0 R)).supportWithinDomain (Function.mem_support.mpr hdu)
  -- the Blaschke product has modulus 1 on the sphere.
  have hB1 : ∀ w ∈ sphere (0 : ℂ) R,
      ‖(∏ᶠ u, (canonicalFactor R u) ^ (-(divisor f (ball 0 R) u))) w‖ = 1 :=
    fun w hw => norm_finprod_canonicalFactor_zpow_eq_one _ hfin hsupp hw
  -- the agreement set is codiscrete, hence dense in the sphere.
  have hcod : {w | f w = (∏ᶠ u, (canonicalFactor R u) ^ (-(divisor f (ball 0 R) u))) w • g w}
      ∈ codiscreteWithin (closedBall (0 : ℂ) R) := D.eventuallyEq
  have hdense := dense_inter_sphere_of_codiscrete hR hcod
  exact norm_eq_of_codiscrete_factor_on_sphere hcont_f hcont_g hB1 hdense hz
