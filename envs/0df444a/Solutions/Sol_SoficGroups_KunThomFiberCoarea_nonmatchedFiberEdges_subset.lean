-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.nonmatchedFiberEdges_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/9f075de9-b256-41a8-9b16-3d7720f6e5e8

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
    U \ matchedFiberEdges U ⊆
      nonSingletonFirstEdges U ∪ nonSingletonSecondEdges U := by
  classical
  intro z hz
  obtain ⟨hzU, hznot⟩ := Finset.mem_sdiff.mp hz
  have hnot : ¬ (firstMultiplicity U z.1 = 1 ∧
      secondMultiplicity U z.2 = 1) := by
    intro h
    apply hznot
    exact Finset.mem_filter.mpr ⟨hzU, h⟩
  by_cases hfirst : firstMultiplicity U z.1 = 1
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨hzU, fun hsecond => hnot ⟨hfirst, hsecond⟩⟩
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hzU, hfirst⟩
end SoficGroups.KunThomFiberCoarea
