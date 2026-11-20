-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.squarePartitionBComponent_regionErasureRecoverable_of_allFitting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:48:04.458115+00:00
-- url     : https://prove2.me/submissions/03cca5fa-e829-4c46-9883-948259d371c0

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionBComponent_eq_tile_sdiff_C_of_odd
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allFitting

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
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin tileRows tileColumns : Nat}
    (hblockWidth : 0 < blockWidth)
    (hrows : L.lattice.rows = tileRows * blockWidth)
    (hcolumns : L.lattice.columns = tileColumns * blockWidth)
    (hall : M.AllFittingSquaresRecoverable blockWidth) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionBComponents blockWidth margin) :
    M.RegionErasureRecoverable block := by
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hblock).1 with ⟨index, hindex, rfl⟩
  have hoccupied : index ∈ L.lattice.occupiedTileIndices blockWidth :=
    (Finset.mem_filter.mp hindex).1
  have hodd : ¬ Even (index.1 + index.2) := (Finset.mem_filter.mp hindex).2
  rw [L.lattice.squarePartitionBComponent_eq_tile_sdiff_C_of_odd
    hblockWidth margin index hodd]
  exact M.tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allFitting
    hblockWidth hrows hcolumns hall index hoccupied
end QEC.Bounds.BPTCommutingProjectorModel
