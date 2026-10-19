-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.normalizedPairDisplacement_inner_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/797378f1-4981-4503-91df-a1af6eac3780

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_normalizedPairDisplacement_diagonal

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {G ι V : Type*} [Group G] [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (a g h j k : G)
    (hg : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * g) x = (σ a * σ g) x)
    (hh : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * h) x = (σ a * σ h) x)
    (hj : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * j) x = (σ a * σ j) x)
    (hk : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * k) x = (σ a * σ k) x) :
    @inner ℂ (EuclideanSpace ℂ V) _
      (normalizedPairDisplacement p f σ (a * g, a * h))
      (normalizedPairDisplacement p f σ (a * j, a * k)) =
    @inner ℂ (EuclideanSpace ℂ V) _
      (normalizedPairDisplacement p f σ (g, h))
      (normalizedPairDisplacement p f σ (j, k)) := by
  rw [normalizedPairDisplacement_diagonal p f σ a g h hg hh,
    normalizedPairDisplacement_diagonal p f σ a j k hj hk]
  exact (permutationUnitary (σ a)).inner_map_map _ _
end SoficGroups.KunRootedIndicatorCrossing
