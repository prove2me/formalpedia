-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.permutationUnitary_eq_of_agree_on_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/9ee3a9ec-7043-4c71-9f68-75035363ae6e

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {V : Type*} [Fintype V] (p q : Equiv.Perm V)
    (ξ : EuclideanSpace ℂ V)
    (h : ∀ x : V, ξ x ≠ 0 → p x = q x) :
    permutationUnitary p ξ = permutationUnitary q ξ := by
  ext y
  change ξ (p.symm y) = ξ (q.symm y)
  by_cases hp : ξ (p.symm y) = 0
  · rw [hp]
    have hzero : ξ (q.symm y) = 0 := by
      by_contra hq
      have hsame : q.symm y = p.symm y := by
        apply p.injective
        simpa using h (q.symm y) hq
      apply hq
      rw [hsame]
      exact hp
    exact hzero.symm
  · have hsame : p.symm y = q.symm y := by
      apply q.injective
      simpa using (h (p.symm y) hp).symm
    rw [hsame]
end SoficGroups.KunRootedIndicatorCrossing
