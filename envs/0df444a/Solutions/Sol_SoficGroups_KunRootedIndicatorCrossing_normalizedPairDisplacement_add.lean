-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.normalizedPairDisplacement_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/fd53f408-5b43-4962-8582-c4a762d1c583

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
    {G ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (g h j : G) :
    normalizedPairDisplacement p f σ (g, h) +
      normalizedPairDisplacement p f σ (h, j) =
        normalizedPairDisplacement p f σ (g, j) := by
  unfold normalizedPairDisplacement
  abel
end SoficGroups.KunRootedIndicatorCrossing
