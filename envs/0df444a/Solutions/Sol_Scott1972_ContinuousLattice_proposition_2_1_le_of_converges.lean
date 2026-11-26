-- Prove2me | solution 1 for Scott1972.ContinuousLattice.proposition_2_1_le_of_converges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:31:12.533596+00:00
-- url     : https://prove2.me/submissions/33b3412f-67a9-42c7-87e3-4f35d75776b3

import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.DirSupClosed
import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_not_le

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]
variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
variable {x : ι → D} {L y : D}
omit [IsDirected ι (· ≤ ·)]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hL : IsLUB (range x) L)
    (hconv : ScottConvergesTo x y) : y ≤ L := by
  by_contra hyL
  obtain ⟨i, hi⟩ := hconv {z : D | ¬ z ≤ L} (scottOpen_not_le L) hyL
  exact hi i le_rfl (hL.1 ⟨i, rfl⟩)
end Scott1972.ContinuousLattice
