-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.disjoint_clean_parts_singleton_bad_parts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/1f347009-03d3-4f82-a7fc-5ecb1607f754

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunResidualExpanderDecomposition
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (P : Finpartition (Finset.univ \ B)) :
    Disjoint P.parts (⊥ : Finpartition B).parts := by
  apply Finset.disjoint_left.mpr
  intro C hCP hCB
  obtain ⟨x, hxB, hxC⟩ := Finpartition.mem_bot_iff.mp hCB
  subst C
  have hxclean := P.subset hCP (Finset.mem_singleton_self x)
  exact (Finset.mem_sdiff.mp hxclean).2 hxB
end SoficGroups.KunResidualExpanderDecomposition
