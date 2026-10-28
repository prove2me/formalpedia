-- Prove2me | solution 1 for ZeroFreeBridge.norm_finprod_canonicalFactor_zpow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:31.899398+00:00
-- url     : https://prove2.me/submissions/c364e60c-83f1-4eca-8608-be5368278548

import Mathlib

/- PHASE 4 (dVP frontier, BLASCHKE correction): the finite Blaschke product has modulus 1 on the
   sphere — the fact that removes the lossy AP term.

   The monomial factorization `ζ = ∏(·-ρ)^m · g` fails to give `M' = O(L)`: near a boundary zero the
   decomposition `log‖g‖ = log‖ζ‖ - log‖P‖` throws away a cancellation, so `AP` blows up.  The
   classical fix uses BLASCHKE factors, and Mathlib already has them:
   `canonicalFactor R w z = (R² - conj w · z)/(R(z-w))` (`Analysis/Complex/CanonicalDecomposition`),
   with `‖canonicalFactor R w z‖ = 1` for `z ∈ sphere 0 R`, `w ∈ ball 0 R`
   (`norm_canonicalFactor_eval_circle_eq_one`), and the full decomposition `MeromorphicOn.exists_
   canonicalDecomp`: `f =ᶠ (∏ᶠ_u canonicalFactor^{-divisor u}) • g` with `g` zero-free on the ball.

   This file lifts the single-factor modulus-1 fact to the whole finite product: for a finitely
   supported exponent `n` with support in `ball 0 R`,
     `‖(∏ᶠ_u (canonicalFactor R u)^{n u}) z‖ = 1`   for   `z ∈ sphere 0 R`.
   Consequently `‖f‖ = ‖g‖` on the sphere (up to the codiscrete exceptional set) — so the boundary
   `M'` is `sup log‖f‖ - log‖g c‖ = O(L)` with NO zero-factor term.  conjecture1_proved = False.
-/


open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {R : ℝ} (n : ℂ → ℤ)
    (hn : (Function.support n).Finite)
    (hsupp : ∀ u ∈ hn.toFinset, u ∈ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    ‖(∏ᶠ u, (canonicalFactor R u) ^ (n u)) z‖ = 1 := by
  -- finprod of the (Pi-zpow) functions collapses to a Finset product.
  have hFP : (∏ᶠ u, (canonicalFactor R u) ^ (n u))
      = fun w => ∏ u ∈ hn.toFinset, (canonicalFactor R u w) ^ (n u) := by
    have hsub : Function.mulSupport (fun u => (canonicalFactor R u) ^ (n u)) ⊆ hn.toFinset := by
      intro u hu
      rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
      intro hnu
      apply hu
      funext w
      simp [hnu]
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    funext w
    exact Finset.prod_apply w hn.toFinset _
  rw [hFP, norm_prod]
  refine Finset.prod_eq_one (fun u hu => ?_)
  rw [norm_zpow, norm_canonicalFactor_eval_circle_eq_one (hsupp u hu) hz, one_zpow]
