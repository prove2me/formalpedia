-- Prove2me | solution 1 for SoficGroups.KunAdditiveMedianPoincare.permutationRealVariation_positive_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/60693417-af52-48f4-b2ca-09bfd46feb90

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_positive_negative_abs_eq

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunAdditiveMedianPoincare
open SoficGroups.CheegerPoincare
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunAdditiveMedianPoincare
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (m : ℝ) :
    permutationRealVariation σ (fun x => max (f x - m) 0) +
      permutationRealVariation σ (fun x => max (m - f x) 0) =
        permutationRealVariation σ f := by
  unfold permutationRealVariation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hx : m - f x = -(f x - m) := by ring
  have hy : m - f (σ i x) = -(f (σ i x) - m) := by ring
  have hxy :
      (f (σ i x) - m) - (f x - m) = f (σ i x) - f x := by
    ring
  simpa only [hx, hy, hxy] using
    positive_negative_abs_eq (f (σ i x) - m) (f x - m)
end SoficGroups.KunAdditiveMedianPoincare
