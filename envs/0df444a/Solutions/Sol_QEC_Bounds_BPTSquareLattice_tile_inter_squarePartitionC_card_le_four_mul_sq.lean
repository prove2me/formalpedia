-- Prove2me | solution 1 for QEC.Bounds.BPTSquareLattice.tile_inter_squarePartitionC_card_le_four_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:46:17.586989+00:00
-- url     : https://prove2.me/submissions/201634a6-a4e5-4b0e-b7a4-28a74b688736

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_rectangle_card_le_area
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_tile_inter_squarePartitionC_subset_cornerCutoutTileCover

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTSquareLattice
namespace QEC.Bounds.BPTSquareLattice
theorem _root_.solution (L : BPTSquareLattice)
    {blockWidth margin : Nat} (hblockWidth : 0 < blockWidth) (hmargin : margin ≤ blockWidth)
    (index : Nat × Nat) :
    (L.tile blockWidth index ∩ L.squarePartitionC blockWidth margin).card ≤
      4 * margin * margin := by
  have hsubset := L.tile_inter_squarePartitionC_subset_cornerCutoutTileCover
    hblockWidth hmargin index
  have hLowerLower :
      (L.rectangle (index.1 * blockWidth, index.2 * blockWidth) margin margin).card ≤
        margin * margin :=
    L.rectangle_card_le_area _ _ _
  have hLowerUpper :
      (L.rectangle (index.1 * blockWidth, index.2 * blockWidth + blockWidth - margin)
        margin margin).card ≤ margin * margin :=
    L.rectangle_card_le_area _ _ _
  have hUpperLower :
      (L.rectangle (index.1 * blockWidth + blockWidth - margin, index.2 * blockWidth)
        margin margin).card ≤ margin * margin :=
    L.rectangle_card_le_area _ _ _
  have hUpperUpper :
      (L.rectangle (index.1 * blockWidth + blockWidth - margin,
        index.2 * blockWidth + blockWidth - margin) margin margin).card ≤ margin * margin :=
    L.rectangle_card_le_area _ _ _
  have hcover : (L.cornerCutoutTileCover blockWidth margin index).card ≤
      margin * margin + margin * margin + margin * margin + margin * margin := by
    calc
      (L.cornerCutoutTileCover blockWidth margin index).card =
          (((L.rectangle (index.1 * blockWidth, index.2 * blockWidth) margin margin ∪
            L.rectangle (index.1 * blockWidth, index.2 * blockWidth + blockWidth - margin)
              margin margin) ∪
              L.rectangle (index.1 * blockWidth + blockWidth - margin,
                index.2 * blockWidth) margin margin) ∪
                L.rectangle (index.1 * blockWidth + blockWidth - margin,
                  index.2 * blockWidth + blockWidth - margin) margin margin).card := rfl
      _ ≤ ((L.rectangle (index.1 * blockWidth, index.2 * blockWidth) margin margin ∪
          L.rectangle (index.1 * blockWidth, index.2 * blockWidth + blockWidth - margin)
            margin margin) ∪
            L.rectangle (index.1 * blockWidth + blockWidth - margin,
              index.2 * blockWidth) margin margin).card +
              (L.rectangle (index.1 * blockWidth + blockWidth - margin,
                index.2 * blockWidth + blockWidth - margin) margin margin).card :=
        Finset.card_union_le _ _
      _ ≤ ((L.rectangle (index.1 * blockWidth, index.2 * blockWidth) margin margin ∪
          L.rectangle (index.1 * blockWidth, index.2 * blockWidth + blockWidth - margin)
            margin margin).card +
            (L.rectangle (index.1 * blockWidth + blockWidth - margin,
              index.2 * blockWidth) margin margin).card) +
              (L.rectangle (index.1 * blockWidth + blockWidth - margin,
                index.2 * blockWidth + blockWidth - margin) margin margin).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ ((L.rectangle (index.1 * blockWidth, index.2 * blockWidth) margin margin).card +
          (L.rectangle (index.1 * blockWidth, index.2 * blockWidth + blockWidth - margin)
            margin margin).card +
            (L.rectangle (index.1 * blockWidth + blockWidth - margin,
              index.2 * blockWidth) margin margin).card) +
              (L.rectangle (index.1 * blockWidth + blockWidth - margin,
                index.2 * blockWidth + blockWidth - margin) margin margin).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ (margin * margin + margin * margin + margin * margin) + margin * margin := by
        gcongr
      _ = margin * margin + margin * margin + margin * margin + margin * margin := by omega
  calc
    (L.tile blockWidth index ∩ L.squarePartitionC blockWidth margin).card ≤
        (L.cornerCutoutTileCover blockWidth margin index).card := Finset.card_le_card hsubset
    _ ≤ margin * margin + margin * margin + margin * margin + margin * margin := hcover
    _ = 4 * margin * margin := by ring
end QEC.Bounds.BPTSquareLattice
