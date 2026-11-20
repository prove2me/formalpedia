-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.allSquareBlocksRecoverable_of_width_sq_lt_measurementDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:46:24.007199+00:00
-- url     : https://prove2.me/submissions/4b7c7b25-a921-4356-bbe4-0c7959c6bcfb

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_square_regionErasureRecoverable_of_width_sq_lt_measurementDistance

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
    (M : BPTCommutingProjectorModel L kappa) (distance width : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hwidth : width * width < distance) :
    M.AllSquareBlocksRecoverable width := by
  intro origin
  exact M.square_regionErasureRecoverable_of_width_sq_lt_measurementDistance
    distance hDistance origin width hwidth
end QEC.Bounds.BPTCommutingProjectorModel
