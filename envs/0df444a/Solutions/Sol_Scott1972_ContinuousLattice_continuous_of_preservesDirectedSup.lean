-- Prove2me | solution 1 for Scott1972.ContinuousLattice.continuous_of_preservesDirectedSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:32:27.774011+00:00
-- url     : https://prove2.me/submissions/a420ae9b-7d11-4d1a-874e-c1462e414ad5

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_preimage
import Theorems.Thm_Scott1972_ContinuousLattice_isOpen_iff_scottOpen


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
namespace Scott1972.ContinuousLattice
theorem _root_.solution {f : D → D'} (hf : PreservesDirectedSup f) :
    @Continuous D D' scottTopologicalSpace scottTopologicalSpace f := by
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_scottOpen] at hU ⊢
  exact scottOpen_preimage hf hU
end Scott1972.ContinuousLattice
