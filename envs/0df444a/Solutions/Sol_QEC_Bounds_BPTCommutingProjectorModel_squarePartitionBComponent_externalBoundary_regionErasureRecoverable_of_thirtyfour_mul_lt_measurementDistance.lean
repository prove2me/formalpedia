-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.squarePartitionBComponent_externalBoundary_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:03:22.108532+00:00
-- url     : https://prove2.me/submissions/d850be10-f141-40aa-86bc-4b017e0f802c

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionBComponent_eq_tile_sdiff_C_of_odd
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance

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
    {blockWidth margin : Nat} (hblockWidth : 0 < blockWidth)
    (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth)
    (hthin : 34 * margin * blockWidth < distance) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionBComponents blockWidth margin) :
    M.RegionErasureRecoverable (M.externalBoundary block) := by
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, hindex, rfl⟩
  have hodd : ¬ Even (index.1 + index.2) := (Finset.mem_filter.mp hindex).2
  rw [L.lattice.squarePartitionBComponent_eq_tile_sdiff_C_of_odd
    hblockWidth margin index hodd]
  exact M.externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
    distance hDistance hblockWidth hmargin hwidth hthin index
end QEC.Bounds.BPTCommutingProjectorModel
