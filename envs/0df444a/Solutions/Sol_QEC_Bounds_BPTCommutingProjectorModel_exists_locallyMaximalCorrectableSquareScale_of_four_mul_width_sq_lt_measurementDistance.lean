-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.exists_locallyMaximalCorrectableSquareScale_of_four_mul_width_sq_lt_measurementDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:50:49.86187+00:00
-- url     : https://prove2.me/submissions/7ff2a7ee-1504-49f5-92de-6d68cd79de7b

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_locallyMaximalCorrectableSquareScale
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_allSquareBlocksRecoverable_of_width_sq_lt_measurementDistance

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
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (distance : Nat) (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hseed : (4 * M.interactionRange) * (4 * M.interactionRange) < distance)
    (hpositive : 0 < parameter.encodedQubits) :
    ∃ width, 4 * M.interactionRange ≤ width ∧
      M.LocallyMaximalCorrectableSquareScale width := by
  apply M.exists_locallyMaximalCorrectableSquareScale parameter ?_ hpositive
  exact M.allSquareBlocksRecoverable_of_width_sq_lt_measurementDistance distance
    (4 * M.interactionRange) hDistance hseed
end QEC.Bounds.BPTCommutingProjectorModel
