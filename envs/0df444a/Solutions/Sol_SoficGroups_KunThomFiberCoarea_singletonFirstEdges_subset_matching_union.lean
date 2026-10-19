-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.singletonFirstEdges_subset_matching_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/68ec2888-3263-430f-8e4e-a187a4a29359

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) :
    singletonFirstEdges U ⊆
      matchedFiberEdges U ∪ nonSingletonSecondEdges U := by
  classical
  intro z hz
  obtain ⟨hzU, hrow⟩ := Finset.mem_filter.mp hz
  by_cases hcol : secondMultiplicity U z.2 = 1
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hzU, hrow, hcol⟩
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hzU, hcol⟩
end SoficGroups.KunThomFiberCoarea
