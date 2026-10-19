-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.normalizedPairDisplacement_generator_of_model
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/b0e1e135-926b-44f4-95ca-a8fb19cf8996

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
    {G ι V : Type*} [Group G] [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (s : ι → G)
    (hone : σ 1 = 1) (hgenerator : ∀ i, σ (s i) = p i)
    (i : ι) :
    normalizedPairDisplacement p f σ (s i, 1) =
      normalizedIndicatorDisplacement p f (p i) := by
  simp [normalizedPairDisplacement, normalizedIndicatorDisplacement,
    hone, hgenerator]
end SoficGroups.KunRootedIndicatorCrossing
