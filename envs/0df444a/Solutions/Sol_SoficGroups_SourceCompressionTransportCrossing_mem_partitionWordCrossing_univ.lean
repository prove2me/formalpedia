-- Prove2me | solution 1 for SoficGroups.SourceCompressionTransportCrossing.mem_partitionWordCrossing_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/7270da36-b8ba-4a0c-a5de-f5c18cab829a

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionTransportCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCompressionTransportCrossing
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
end SoficGroups.SourceCompressionTransportCrossing
