-- Prove2me | solution 1 for Scott1972.ContinuousLattice.continuous_preservesDirectedSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:29:52.124802+00:00
-- url     : https://prove2.me/submissions/54c75df5-fb15-4098-8152-bb636de4c698

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
namespace Scott1972.ContinuousLattice
theorem _root_.solution {f : D → D'}
    (hf : @Continuous D D' scottTopologicalSpace scottTopologicalSpace f) :
    PreservesDirectedSup f := by
  have hD : @IsScott D univ _ (Topology.scott D univ) :=
    @IsScott.mk D univ _ (Topology.scott D univ) rfl
  have hD' : @IsScott D' univ _ (Topology.scott D' univ) :=
    @IsScott.mk D' univ _ (Topology.scott D' univ) rfl
  have hsc : ScottContinuous f :=
    scottContinuousOn_univ.1 <|
      (@Topology.IsScott.scottContinuousOn_iff_continuous D D' _
        (Topology.scott D univ) _ (Topology.scott D' univ) hD' f univ hD
        (fun _ _ _ => trivial)).2 hf
  intro S hS hSdir
  exact (hsc hS hSdir (isLUB_sSup S)).sSup_eq.symm
end Scott1972.ContinuousLattice
