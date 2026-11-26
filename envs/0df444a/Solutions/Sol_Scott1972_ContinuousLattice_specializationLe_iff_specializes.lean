-- Prove2me | solution 1 for Scott1972.ContinuousLattice.specializationLe_iff_specializes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:31:03.974819+00:00
-- url     : https://prove2.me/submissions/0eb7151f-c52f-4d72-ac95-6e9cb93e2243

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
theorem _root_.solution {x y : X} :
    SpecializationLe x y ↔ y ⤳ x :=
  specializes_iff_forall_open.symm
end Scott1972.ContinuousLattice
