-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_of_measurementDistance_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:20:23.302937+00:00
-- url     : https://prove2.me/submissions/47719b45-96e1-4bf4-b047-0bb63f7d28ef

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Semantics_QuditSubsystem_BPTMeasurementDistance_noInformationOn_of_card_lt
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_iff_exists_erasureRecovery


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
    (region : Finset L.Site) (hcard : region.card < distance) :
    M.RegionErasureRecoverable region := by
  apply ((M.regionSubsystem region).noInformationOn_iff_exists_erasureRecovery
    M.codeSpace L.localDimension_positive).mp
  apply hDistance.noInformationOn_of_card_lt
  change Fintype.card ↥region < distance
  rw [Fintype.card_coe]
  exact hcard
end QEC.Bounds.BPTCommutingProjectorModel
