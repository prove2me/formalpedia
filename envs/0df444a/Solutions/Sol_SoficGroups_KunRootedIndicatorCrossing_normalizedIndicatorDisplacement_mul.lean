-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.normalizedIndicatorDisplacement_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/ffd32e3f-6ad6-4d8d-a690-855d85a7af17

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_permutationUnitary_mul

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (q r : Equiv.Perm V) :
    normalizedIndicatorDisplacement p f (q * r) =
      normalizedIndicatorDisplacement p f q +
        permutationUnitary q (normalizedIndicatorDisplacement p f r) := by
  unfold normalizedIndicatorDisplacement
  rw [permutationUnitary_mul]
  simp only [map_smul, map_sub, smul_sub]
  abel
end SoficGroups.KunRootedIndicatorCrossing
