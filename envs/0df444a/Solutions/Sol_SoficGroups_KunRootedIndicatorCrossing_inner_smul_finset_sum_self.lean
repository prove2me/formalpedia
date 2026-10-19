-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.inner_smul_finset_sum_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/74a71d16-906f-4dd5-9ac3-0f006bbfb220

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
    {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (z : I → E) (F : Finset I) (c : ℂ) :
    ⟪c • ∑ i ∈ F, z i, c • ∑ i ∈ F, z i⟫_ℂ =
      star c * (∑ i ∈ F, ∑ j ∈ F, ⟪z i, z j⟫_ℂ) * c := by
  rw [inner_smul_left, inner_smul_right, sum_inner]
  simp_rw [inner_sum]
  simp only [RCLike.star_def]
  ring
end SoficGroups.KunRootedIndicatorCrossing
