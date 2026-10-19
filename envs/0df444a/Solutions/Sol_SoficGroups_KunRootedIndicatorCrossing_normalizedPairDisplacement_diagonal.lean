-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.normalizedPairDisplacement_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/6e33088f-ec2d-4f1f-b6e8-9292c47c01df

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_normalizedIndicatorDisplacement_cocycle_of_agree_on_support

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
    (σ : G → Equiv.Perm V) (a g h : G)
    (hg : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * g) x = (σ a * σ g) x)
    (hh : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * h) x = (σ a * σ h) x) :
    normalizedPairDisplacement p f σ (a * g, a * h) =
      permutationUnitary (σ a)
        (normalizedPairDisplacement p f σ (g, h)) := by
  unfold normalizedPairDisplacement
  rw [normalizedIndicatorDisplacement_cocycle_of_agree_on_support
    p f σ a g hg,
    normalizedIndicatorDisplacement_cocycle_of_agree_on_support
      p f σ a h hh, map_sub]
  abel
end SoficGroups.KunRootedIndicatorCrossing
