-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.boundary_card_le_sixteen_mul_interactionRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:42:09.365106+00:00
-- url     : https://prove2.me/submissions/4da29212-27d8-43b4-9d9d-e76b9f70d567

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_squareBoundaryFrameStripCover_card_le_sixteen_mul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_subset_squareBoundaryFrameStripCover

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
theorem _root_.solution (M : BPTCommutingProjectorModel L kappa)
    (origin : Nat × Nat) (width : Nat)
    (hwidth : M.interactionRange + M.interactionRange ≤ width) :
    (M.boundary (L.lattice.square origin width)).card ≤
      16 * M.interactionRange * width := by
  calc
    (M.boundary (L.lattice.square origin width)).card ≤
        (L.lattice.squareBoundaryFrameStripCover origin width M.interactionRange).card :=
      Finset.card_le_card (M.boundary_subset_squareBoundaryFrameStripCover origin width hwidth)
    _ ≤ 16 * M.interactionRange * width :=
      L.lattice.squareBoundaryFrameStripCover_card_le_sixteen_mul origin width
        M.interactionRange hwidth
end QEC.Bounds.BPTCommutingProjectorModel
