-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.square_regionErasureRecoverable_of_width_sq_lt_measurementDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:37:53.23764+00:00
-- url     : https://prove2.me/submissions/d6a5a93d-78b0-4433-be05-797d312b8e6d

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_square_card_le_width_sq
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
    (origin : Nat × Nat) (width : Nat) (hwidth : width * width < distance) :
    M.RegionErasureRecoverable (L.lattice.square origin width) := by
  apply M.regionErasureRecoverable_of_measurementDistance_card_lt distance hDistance
  exact (L.lattice.square_card_le_width_sq origin width).trans_lt hwidth
end QEC.Bounds.BPTCommutingProjectorModel
