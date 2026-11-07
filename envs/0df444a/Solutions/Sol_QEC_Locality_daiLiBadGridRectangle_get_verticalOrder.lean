-- Prove2me | solution 1 for QEC.Locality.daiLiBadGridRectangle_get_verticalOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:15:19.897572+00:00
-- url     : https://prove2.me/submissions/9c2818d0-2e7d-4b21-be52-e4bcfbf0d7b3

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_daiLiRectangleList_pairwise_verticalOrder
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_ordered
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_piece_properties


set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    (w ell : ℝ) (origin : ℝ × ℝ) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w origin cell).2 - w / 2)
        ((daiLiGridCellCenter w origin cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w origin,
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w origin cell).1 - w / 2)
        ((daiLiGridCellCenter w origin cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hcell : cell ∈ daiLiBadGridCells P embedding threshold d w origin)
    (first second : ℕ) (hFirst : first < (rectangles cell).length)
    (hSecond : second < (rectangles cell).length) (hOrder : first < second) :
    ((rectangles cell).get ⟨first, hFirst⟩).2.2 ≤
      ((rectangles cell).get ⟨second, hSecond⟩).1.2 := by
  have hChain : (rectangles cell).IsChain (fun left right => left.2.2 = right.1.2) := by
    rw [hRectangles cell hcell]
    exact daiLiPhysicalGreedyRectangles_ordered P embedding threshold
      ((daiLiGridCellCenter w origin cell).1 - w / 2)
      ((daiLiGridCellCenter w origin cell).1 + w / 2) (hAtoms cell hcell) d
  have hNonnegative : ∀ rectangle ∈ rectangles cell,
      0 ≤ rectangle.2.2 - rectangle.1.2 := by
    intro rectangle hRectangle
    have hPhysical := hRectangle
    rw [hRectangles cell hcell] at hPhysical
    have hProperties := daiLiPhysicalGreedyRectangles_piece_properties P embedding threshold
      ((daiLiGridCellCenter w origin cell).1 - w / 2)
      ((daiLiGridCellCenter w origin cell).1 + w / 2) ell hEll
      (hAtoms cell hcell) d rectangle hPhysical
    linarith [hProperties.1]
  have hPairwise := daiLiRectangleList_pairwise_verticalOrder
    (rectangles cell) hChain hNonnegative
  exact hPairwise.rel_get_of_lt (show
    (⟨first, hFirst⟩ : Fin (rectangles cell).length) < ⟨second, hSecond⟩ from hOrder)
end QEC.Locality
