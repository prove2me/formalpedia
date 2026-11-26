-- Prove2me | solution 1 for Scott1972.ContinuousLattice.specializationLe_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:34:10.649663+00:00
-- url     : https://prove2.me/submissions/d0e28545-0459-4926-ac2a-c809d244eb0b

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
theorem _root_.solution [T0Space X] {x y : X}
    (hxy : SpecializationLe x y) (hyx : SpecializationLe y x) : x = y :=
  Inseparable.eq (inseparable_iff_specializes_and.2
    ⟨specializes_iff_forall_open.2 fun s hs hy => hyx s hs hy,
     specializes_iff_forall_open.2 fun s hs hx => hxy s hs hx⟩)
end Scott1972.ContinuousLattice
