-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.squarePartitionAComponent_externalBoundary_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:03:18.69394+00:00
-- url     : https://prove2.me/submissions/381e4b40-c832-4c10-bb22-87b29c8fbe8b

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionAComponent_eq_tile_sdiff_C_of_even
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
    (hblock : block ∈ L.lattice.squarePartitionAComponents blockWidth margin) :
    M.RegionErasureRecoverable (M.externalBoundary block) := by
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, hindex, rfl⟩
  have heven : Even (index.1 + index.2) := (Finset.mem_filter.mp hindex).2
  rw [L.lattice.squarePartitionAComponent_eq_tile_sdiff_C_of_even
    hblockWidth margin index heven]
  exact M.externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
    distance hDistance hblockWidth hmargin hwidth hthin index
end QEC.Bounds.BPTCommutingProjectorModel
