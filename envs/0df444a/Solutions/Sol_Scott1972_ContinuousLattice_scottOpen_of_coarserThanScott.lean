-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottOpen_of_coarserThanScott
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:43:26.37913+00:00
-- url     : https://prove2.me/submissions/55631856-6c57-41fd-9b7f-bbea513f1c78

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Theorems.Thm_Scott1972_ContinuousLattice_isOpen_iff_scottOpen


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']
namespace Scott1972.ContinuousLattice
theorem _root_.solution {τ : TopologicalSpace D} (hτ : CoarserThanScottTopology τ)
    {U : Set D} (hU : @IsOpen D τ U) : ScottOpen U :=
  isOpen_iff_scottOpen.mp (hτ U hU)
end Scott1972.ContinuousLattice
