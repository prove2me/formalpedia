-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.squarePartitionAComponent_regionErasureRecoverable_of_width_sq_lt_measurementDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:46:42.107167+00:00
-- url     : https://prove2.me/submissions/b9861cf8-ac66-4b06-b435-743961d57f54

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionAComponent_card_le_width_sq
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
    (M : BPTCommutingProjectorModel L kappa) (distance blockWidth margin : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hwidth : blockWidth * blockWidth < distance) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionAComponents blockWidth margin) :
    M.RegionErasureRecoverable block := by
  apply M.regionErasureRecoverable_of_measurementDistance_card_lt distance hDistance
  exact (L.lattice.squarePartitionAComponent_card_le_width_sq blockWidth margin block hblock).trans_lt hwidth
end QEC.Bounds.BPTCommutingProjectorModel
