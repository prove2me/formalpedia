-- Prove2me | solution 1 for SoficGroups.SourceCompressionMatching.card_symmDiff_add_twice_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/3c4f9a48-7638-4f65-8878-1c194a28da1e

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionMatching
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.SourceCompressionMatching
theorem _root_.solution
    {V : Type*} [DecidableEq V] (C D : Finset V) :
    (C ∆ D).card + 2 * (C ∩ D).card = C.card + D.card := by
  have hdis : Disjoint (C \ D) (D \ C) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have hsym : (C ∆ D).card = (C \ D).card + (D \ C).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdis]
  have hC := Finset.card_sdiff_add_card_inter C D
  have hD := Finset.card_sdiff_add_card_inter D C
  rw [Finset.inter_comm D C] at hD
  omega
end SoficGroups.SourceCompressionMatching
