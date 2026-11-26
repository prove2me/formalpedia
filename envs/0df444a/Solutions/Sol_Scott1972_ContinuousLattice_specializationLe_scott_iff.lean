-- Prove2me | solution 1 for Scott1972.ContinuousLattice.specializationLe_scott_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:32:33.667404+00:00
-- url     : https://prove2.me/submissions/23207e55-4b7d-46d3-8249-6b4484c0f997

import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.DirSupClosed
import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Theorems.Thm_Scott1972_ContinuousLattice_isOpen_iff_scottOpen
import Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_not_le

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]
variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
variable {x : ι → D} {L y : D}
namespace Scott1972.ContinuousLattice
theorem _root_.solution {x y : D} :
    @SpecializationLe D scottTopologicalSpace x y ↔ x ≤ y := by
  constructor
  · intro hxy
    by_contra h
    exact hxy {z | ¬ z ≤ y} (isOpen_iff_scottOpen.mpr (scottOpen_not_le y)) h (by simp)
  · intro hxy U hU hxU
    exact (isOpen_iff_scottOpen.mp hU).1 hxy hxU
end Scott1972.ContinuousLattice
