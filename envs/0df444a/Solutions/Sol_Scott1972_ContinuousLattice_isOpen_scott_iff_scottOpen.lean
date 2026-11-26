-- Prove2me | solution 1 for Scott1972.ContinuousLattice.isOpen_scott_iff_scottOpen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:34:17.387144+00:00
-- url     : https://prove2.me/submissions/3b6c125f-10c7-412b-86a3-48f72b4de578

import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.DirSupClosed
import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Theorems.Thm_Scott1972_ContinuousLattice_isOpen_iff_scottOpen

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution {U : Set D} :
    @IsOpen D (Topology.scott D univ) U ↔ ScottOpen U :=
  isOpen_iff_scottOpen
end Scott1972.ContinuousLattice
