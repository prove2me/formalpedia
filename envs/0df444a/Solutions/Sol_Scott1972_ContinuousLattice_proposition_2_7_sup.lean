-- Prove2me | solution 1 for Scott1972.ContinuousLattice.proposition_2_7_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:42:43.833152+00:00
-- url     : https://prove2.me/submissions/8580a155-5cc8-4300-a4d9-c73bde9b66c8

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Theorems.Thm_Scott1972_ContinuousLattice_continuous_of_preservesDirectedSup

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
namespace Scott1972.ContinuousLattice
theorem _root_.solution :
    @Continuous (D × D) D scottTopologicalSpace scottTopologicalSpace (fun p : D × D => p.1 ⊔ p.2) :=
  continuous_of_preservesDirectedSup <| by
    intro S hS hSdir
    simpa using (ScottContinuous.sup₂ (β := D) (d := S) hS hSdir (isLUB_sSup S)).sSup_eq.symm
end Scott1972.ContinuousLattice
