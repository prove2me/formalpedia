-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_squarePartitionBComponents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:55:45.184958+00:00
-- url     : https://prove2.me/submissions/27e605a6-a30a-40e6-a430-6cf2dcf5e347

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_squarePartitionBComponent_of_odd_distinct
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_actualProjectorSeparated_of_coordinateRangeSeparated

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
    (M : BPTCommutingProjectorModel L kappa) {blockWidth : Nat}
    (hblockWidth : 0 < blockWidth) (margin : Nat)
    (hrangeBlock : M.interactionRange ≤ blockWidth)
    (hrangeMargin : M.interactionRange ≤ margin)
    (left : Finset L.Site)
    (hleft : left ∈ L.lattice.squarePartitionBComponents blockWidth margin)
    (right : Finset L.Site)
    (hright : right ∈ L.lattice.squarePartitionBComponents blockWidth margin)
    (hne : left ≠ right) :
    M.ActualProjectorSeparated left right := by
  apply M.actualProjectorSeparated_of_coordinateRangeSeparated
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hleft).1 with ⟨leftIndex, hleftIndex, rfl⟩
  rcases Finset.mem_image.mp (Finset.mem_filter.mp hright).1 with
    ⟨rightIndex, hrightIndex, rfl⟩
  have hoddLeft : ¬ Even (leftIndex.1 + leftIndex.2) :=
    (Finset.mem_filter.mp hleftIndex).2
  have hoddRight : ¬ Even (rightIndex.1 + rightIndex.2) :=
    (Finset.mem_filter.mp hrightIndex).2
  have hindexNe : leftIndex ≠ rightIndex := by
    intro heq
    subst rightIndex
    exact hne rfl
  exact L.lattice.coordinateRangeSeparated_squarePartitionBComponent_of_odd_distinct
    hblockWidth hrangeBlock hrangeMargin leftIndex rightIndex hoddLeft hoddRight hindexNe
end QEC.Bounds.BPTCommutingProjectorModel
