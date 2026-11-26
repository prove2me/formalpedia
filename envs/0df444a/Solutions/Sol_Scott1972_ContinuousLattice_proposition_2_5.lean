-- Prove2me | solution 1 for Scott1972.ContinuousLattice.proposition_2_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:32:56.592526+00:00
-- url     : https://prove2.me/submissions/fd1601c5-b7f1-4e9b-b857-cef613684e42

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Theorems.Thm_Scott1972_ContinuousLattice_continuous_of_preservesDirectedSup
import Theorems.Thm_Scott1972_ContinuousLattice_continuous_preservesDirectedSup

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
namespace Scott1972.ContinuousLattice
theorem _root_.solution (f : D → D') :
    (@Continuous D D' scottTopologicalSpace scottTopologicalSpace f) ↔
      PreservesDirectedSup f :=
  ⟨continuous_preservesDirectedSup, fun hf => continuous_of_preservesDirectedSup hf⟩
end Scott1972.ContinuousLattice
