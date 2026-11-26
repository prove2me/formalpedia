-- Prove2me | solution 1 for Scott1972.ContinuousLattice.proposition_2_7_inf_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:43:04.98594+00:00
-- url     : https://prove2.me/submissions/369f9f20-6135-48b7-bc51-98eb49347fff

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
theorem _root_.solution (hD : IsContinuousLattice D) (x : D) :
    @Continuous D D scottTopologicalSpace scottTopologicalSpace (fun y => x ⊓ y) :=
  continuous_of_preservesDirectedSup (meet_preservesDirectedSup x hD)
end Scott1972.ContinuousLattice
