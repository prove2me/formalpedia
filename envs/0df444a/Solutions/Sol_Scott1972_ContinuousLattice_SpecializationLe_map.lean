-- Prove2me | solution 1 for Scott1972.ContinuousLattice.SpecializationLe.map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:31:06.105026+00:00
-- url     : https://prove2.me/submissions/6570ef67-9ca9-4806-abed-64057fe036fa

import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.DirSupClosed
import Definitions.Def_Scott1972_ContinuousLattice_Specialization

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]
namespace Scott1972.ContinuousLattice
namespace SpecializationLe
theorem _root_.solution {Y : Type*} [TopologicalSpace Y] {x y : X}
    (hxy : SpecializationLe x y) {f : X → Y} (hf : Continuous f) :
    SpecializationLe (f x) (f y) := by
  intro U hU hxU
  exact hxy (f ⁻¹' U) (hU.preimage hf) hxU
end SpecializationLe
end Scott1972.ContinuousLattice
