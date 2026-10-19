-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.normalizedIndicatorDisplacement_cocycle_of_agree_on_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/0bed8118-ebad-4c34-99b7-66cc7d95ba1b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_permutationUnitary_model_mul_of_agree_on_support

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
    (σ : G → Equiv.Perm V) (a g : G)
    (hroot : ∀ x : V, indicatorVector f x ≠ 0 →
      σ (a * g) x = (σ a * σ g) x) :
    normalizedIndicatorDisplacement p f (σ (a * g)) =
      normalizedIndicatorDisplacement p f (σ a) +
        permutationUnitary (σ a)
          (normalizedIndicatorDisplacement p f (σ g)) := by
  unfold normalizedIndicatorDisplacement
  rw [permutationUnitary_model_mul_of_agree_on_support
    σ a g (indicatorVector f) hroot]
  simp only [map_smul, map_sub, smul_sub]
  abel
end SoficGroups.KunRootedIndicatorCrossing
