-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.inner_smul_fintype_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/4145f837-47e8-43be-a6ed-8bd0aed458df

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : ι → E) (c : ℂ) :
    ⟪c • ∑ i, x i, c • ∑ j, y j⟫_ℂ =
      star c * (∑ i, ∑ j, ⟪x i, y j⟫_ℂ) * c := by
  rw [inner_smul_left, inner_smul_right, sum_inner]
  simp_rw [inner_sum]
  simp only [RCLike.star_def]
  ring
end SoficGroups.KunRootedWordPower
