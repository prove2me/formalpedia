-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.permutationUnitary_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/5fa0b796-0cc6-4d2d-93f3-dc91575030d3

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
theorem _root_.solution {V : Type*} [Fintype V]
    (p q : Equiv.Perm V) (ξ : EuclideanSpace ℂ V) :
    permutationUnitary (p * q) ξ =
      permutationUnitary p (permutationUnitary q ξ) := by
  ext x
  change ξ ((p * q).symm x) = ξ (q.symm (p.symm x))
  rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply]
end SoficGroups.KunRootedIndicatorCrossing
