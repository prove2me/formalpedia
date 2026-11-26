-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottTopology_t0Space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:33:19.763445+00:00
-- url     : https://prove2.me/submissions/3e469b28-a239-4740-9aa3-2fea944f16cb

import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.DirSupClosed
import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Theorems.Thm_Scott1972_ContinuousLattice_specializationLe_scott_iff

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]
variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
variable {x : ι → D} {L y : D}
namespace Scott1972.ContinuousLattice
theorem _root_.solution : @T0Space D scottTopologicalSpace := by
  letI : TopologicalSpace D := scottTopologicalSpace
  constructor
  intro x y hxy
  apply le_antisymm
  · rw [← specializationLe_scott_iff]
    intro U hU hxU
    exact (hxy.mem_open_iff hU).mp hxU
  · rw [← specializationLe_scott_iff]
    intro U hU hyU
    exact (hxy.mem_open_iff hU).mpr hyU
end Scott1972.ContinuousLattice
