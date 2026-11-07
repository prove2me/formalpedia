-- Prove2me | solution 1 for QEC.Locality.daiLiKGeD_cell_assignment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:27:42.681088+00:00
-- url     : https://prove2.me/submissions/d8971e79-6998-444d-84db-2ffc773e850b

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_daiLiGridCellClosedQubits_eq_rectangle
import Theorems.Thm_QEC_Locality_gridCellQubits_subset_daiLiGridCellClosedQubits
import Theorems.Thm_QEC_Locality_daiLiVertexNeighborhoodQubits_subset_badGridRectangleVertexBuffer
import Theorems.Thm_QEC_Locality_daiLiRectanglePoint_vertex_or_strictCore_or_side
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCandidates_good_iff
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCandidates_bad_iff
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDBadRectangleCore_into_A
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDBadRectangle_leftSide_into_B
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDBadRectangle_rightSide_into_B
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDBadRectangle_topSide_into_B
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDBadRectangle_bottomSide_into_B
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDGoodCellSide_into_B
import Theorems.Thm_QEC_Locality_exists_daiLiBadGridRectangle_covering_qubit
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDGoodCellCore_into_A
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDGoodCellVertex_into_separator

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
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hw : 0 < w) (hEll : 0 < ell) (cell : ℤ × ℤ)
    (hCell : cell ∈ embedding.gridOccupiedCells w (gridOrigin w t)) (q : ι)
    (hq : q ∈ embedding.gridCellQubits w (gridOrigin w t) cell) :
    q ∈ daiLiKGeDSeparator P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles ∨
      q ∈ (daiLiKGeDASubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected ∨
        q ∈ (daiLiKGeDBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected := by
  by_cases hSeparator : q ∈ daiLiKGeDSeparator P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
  · exact Or.inl hSeparator
  have hRect : q ∈ embedding.qubitsInRectangle
      (gridCellLower w (gridOrigin w t) cell) (gridCellUpper w (gridOrigin w t) cell) := by
    rw [← daiLiGridCellClosedQubits_eq_rectangle]
    exact gridCellQubits_subset_daiLiGridCellClosedQubits embedding hw (gridOrigin w t) cell hq
  by_cases hBad : cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t)
  · rcases exists_daiLiBadGridRectangle_covering_qubit P embedding d threshold w ell t atoms
      rectangles hAtoms hRectangles hw hEll cell hBad q hq with ⟨slot, hqRectangle⟩
    rcases daiLiRectanglePoint_vertex_or_strictCore_or_side embedding ell hEll
      ((rectangles cell).get slot).1 ((rectangles cell).get slot).2 q hqRectangle with
        hVertex | hStrict | ⟨side, hSide⟩
    · rcases hVertex with ⟨vertex, hVertex⟩
      apply Or.inl
      apply Finset.mem_union_right
      exact daiLiVertexNeighborhoodQubits_subset_badGridRectangleVertexBuffer embedding ell
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles cell hBad
        slot.1 slot.2 vertex hVertex
    · apply Or.inr
      apply Or.inl
      have hCandidate : Sum.inr (cell, slot.1) ∈ daiLiKGeDRegionCandidates P embedding threshold d
          w (gridOrigin w t) rectangles :=
        (mem_daiLiKGeDRegionCandidates_bad_iff P embedding threshold d w
          (gridOrigin w t) rectangles cell slot.1).2 ⟨hBad, slot.2⟩
      exact mem_daiLiKGeDBadRectangleCore_into_A P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles cell slot.1
        slot.2 hCandidate q hqRectangle hSeparator hStrict
    · apply Or.inr
      apply Or.inr
      fin_cases side
      · exact mem_daiLiKGeDBadRectangle_leftSide_into_B P embedding d threshold w ell t atoms
          rectangles hAtoms hRectangles hEll cell hBad slot.1 slot.2 q hSide hSeparator
      · exact mem_daiLiKGeDBadRectangle_rightSide_into_B P embedding d threshold w ell t atoms
          rectangles hAtoms hRectangles hEll cell hBad slot.1 slot.2 q hSide hSeparator
      · exact mem_daiLiKGeDBadRectangle_bottomSide_into_B P embedding d threshold w ell t atoms
          rectangles hAtoms hRectangles hEll cell hBad slot.1 slot.2 q hSide hSeparator
      · exact mem_daiLiKGeDBadRectangle_topSide_into_B P embedding d threshold w ell t atoms
          rectangles hAtoms hRectangles hEll cell hBad slot.1 slot.2 q hSide hSeparator
  · have hCandidate : Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d
        w (gridOrigin w t) rectangles :=
      (mem_daiLiKGeDRegionCandidates_good_iff P embedding threshold d w
        (gridOrigin w t) rectangles cell).2 ⟨hCell, hBad⟩
    rcases daiLiRectanglePoint_vertex_or_strictCore_or_side embedding ell hEll
      (gridCellLower w (gridOrigin w t) cell) (gridCellUpper w (gridOrigin w t) cell) q hRect with
        hVertex | hStrict | ⟨side, hSide⟩
    · rcases hVertex with ⟨vertex, hVertex⟩
      exact Or.inl (mem_daiLiKGeDGoodCellVertex_into_separator P embedding hw threshold ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles cell vertex q hVertex)
    · exact Or.inr (Or.inl (mem_daiLiKGeDGoodCellCore_into_A P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles cell hCandidate q
        hRect hSeparator hStrict))
    · exact Or.inr (Or.inr (mem_daiLiKGeDGoodCellSide_into_B P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles cell hCell side q
        hSide hSeparator))
end QEC.Locality
