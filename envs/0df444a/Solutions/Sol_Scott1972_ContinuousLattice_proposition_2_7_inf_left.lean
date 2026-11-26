-- Prove2me | solution 1 for Scott1972.ContinuousLattice.proposition_2_7_inf_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:42:59.905883+00:00
-- url     : https://prove2.me/submissions/3e0d6b4d-8252-46e6-aa67-367c478d8dc2

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Theorems.Thm_Scott1972_ContinuousLattice_continuous_of_preservesDirectedSup
import Theorems.Thm_Scott1972_ContinuousLattice_meet_preservesDirectedSup

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hD : IsContinuousLattice D) (y : D) :
    @Continuous D D scottTopologicalSpace scottTopologicalSpace (fun x => x ⊓ y) :=
  continuous_of_preservesDirectedSup <| by
    intro S' hS' hSdir'
    rw [show (fun x => x ⊓ y) = fun z => y ⊓ z from funext fun x => inf_comm x y]
    have h := meet_preservesDirectedSup y hD
    exact h (S := S') hS' hSdir'
end Scott1972.ContinuousLattice
