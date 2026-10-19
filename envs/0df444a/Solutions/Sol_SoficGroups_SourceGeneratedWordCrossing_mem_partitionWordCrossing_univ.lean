-- Prove2me | solution 1 for SoficGroups.SourceGeneratedWordCrossing.mem_partitionWordCrossing_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/68b57241-3166-40e5-8cf7-c8f141695de4

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceGeneratedWordCrossing
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : Equiv.Perm V) (x : V) :
    x ∈ SoficGroups.partitionWordCrossing Q p ↔
      Q.part x ≠ Q.part (p x) := by
  simp only [SoficGroups.partitionWordCrossing, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Q.mem_part_iff_part_eq_part (Finset.mem_univ _)
    (Finset.mem_univ _)]
  simp [eq_comm]
end SoficGroups.SourceGeneratedWordCrossing
