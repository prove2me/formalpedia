-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.squareBoundaryFrameStripCover_regionErasureRecoverable_of_sixteen_mul_lt_measurementDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:42:12.590972+00:00
-- url     : https://prove2.me/submissions/e6099a61-d8e8-4c7f-a597-72b29f5b0b56

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_squareBoundaryFrameStripCover_card_le_sixteen_mul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionErasureRecoverable_of_measurementDistance_card_lt

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (origin : Nat × Nat) (width : Nat)
    (hwidth : M.interactionRange + M.interactionRange ≤ width)
    (hthin : 16 * M.interactionRange * width < distance) :
    M.RegionErasureRecoverable
      (L.lattice.squareBoundaryFrameStripCover origin width M.interactionRange) := by
  apply M.regionErasureRecoverable_of_measurementDistance_card_lt distance hDistance
  exact (L.lattice.squareBoundaryFrameStripCover_card_le_sixteen_mul origin width
    M.interactionRange hwidth).trans_lt hthin
end QEC.Bounds.BPTCommutingProjectorModel
