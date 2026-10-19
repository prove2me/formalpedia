-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.permutationUnitary_model_mul_of_agree_on_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/56a7e632-e26a-45e1-b45a-fe04fb9d7e76

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_permutationUnitary_mul
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_permutationUnitary_eq_of_agree_on_support

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {G V : Type*} [Group G] [Fintype V]
    (σ : G → Equiv.Perm V) (a g : G) (ξ : EuclideanSpace ℂ V)
    (hroot : ∀ x : V, ξ x ≠ 0 →
      σ (a * g) x = (σ a * σ g) x) :
    permutationUnitary (σ (a * g)) ξ =
      permutationUnitary (σ a) (permutationUnitary (σ g) ξ) := by
  rw [permutationUnitary_eq_of_agree_on_support
    (σ (a * g)) (σ a * σ g) ξ hroot,
    permutationUnitary_mul]
end SoficGroups.KunRootedIndicatorCrossing
