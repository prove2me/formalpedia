-- Prove2me | solution 1 for ZeroFreeBridge.logDeriv_finprod_canonicalFactor
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:44:59.85795+00:00
-- url     : https://prove2.me/submissions/a3e32852-cf51-4a52-8d70-5f10648ee337

import Mathlib

/- PHASE 4 (dVP frontier, BLASCHKE item (d1)): the log-derivative of the finite Blaschke product
   is the sum of the canonical-factor log-derivatives.

   Mirrors the monomial `DlvpHerglotz.logDeriv_prod_sub_zpow`, but with `canonicalFactor` in place of
   `(·-ρ)`.  For a finitely-supported integer exponent `n`, at a point `z` where each factor is
   differentiable and nonzero,

     `logDeriv (∏ᶠ_u (canonicalFactor R u)^{n u}) z = Σ_u (n u)·logDeriv (canonicalFactor R u) z`.

   Combined with `DlvpCanonicalLogDeriv.logDeriv_canonicalFactor`, each term expands to the Herglotz
   contribution `−(n u)/(z-u)` plus the bounded correction `−(n u)·conj u/(R²-conj u·z)`.  This is the
   Blaschke analog of the obligation-(i) Herglotz sum.  Function-agnostic.  conjecture1_proved = False.
-/


open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {R : ℝ} (n : ℂ → ℤ)
    (hn : (Function.support n).Finite) (z : ℂ)
    (hdiff : ∀ u ∈ hn.toFinset, DifferentiableAt ℂ (canonicalFactor R u) z)
    (hne : ∀ u ∈ hn.toFinset, canonicalFactor R u z ≠ 0) :
    logDeriv (∏ᶠ u, (canonicalFactor R u) ^ (n u)) z
      = ∑ u ∈ hn.toFinset, (n u : ℂ) * logDeriv (canonicalFactor R u) z := by
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
  rw [hFP, logDeriv_prod (f := fun u => fun w : ℂ => (canonicalFactor R u w) ^ (n u))
    (fun u hu => zpow_ne_zero _ (hne u hu))
    (fun u hu => (hdiff u hu).zpow (Or.inl (hne u hu)))]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [logDeriv_fun_zpow (hdiff u hu) (n u)]
