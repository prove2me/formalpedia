-- Prove2me | solution 1 for SoficGroups.KunAdditiveMedianPoincare.additive_permutation_finiteVariance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/9f69d297-2ff2-4182-9890-f39df5ef3165

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CheegerPoincare_card_mul_finiteVariance
import Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_additive_permutation_median_variance

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunAdditiveMedianPoincare
open SoficGroups.CheegerPoincare
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunAdditiveMedianPoincare
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Nonempty V]
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ε : ℝ)
    (hγ : 0 ≤ γ)
    (hε : 0 ≤ ε)
    (hexp : ∀ A : Finset V,
      γ * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ) + ε)
    (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    (hf_one : ∀ x, f x ≤ 1) :
    2 * γ * (Fintype.card V : ℝ) *
        SoficGroups.CheegerPoincare.finiteVariance f ≤
      permutationRealVariation σ f + 4 * ε := by
  have hvariance := additive_permutation_median_variance
    σ γ ε hγ hε hexp f hf hf_one
  rw [← SoficGroups.CheegerPoincare.card_mul_finiteVariance f]
    at hvariance
  nlinarith
end SoficGroups.KunAdditiveMedianPoincare
