-- Prove2me | solution 1 for QEC.Locality.daiLiKGeDResidual_subset_separator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:29:42.320785+00:00
-- url     : https://prove2.me/submissions/1995cf76-eaa0-46f5-ac02-05e7111fbc80

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_daiLiKGeD_cell_assignment
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_gridCellQubits_cover


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
    (hw : 0 < w) (hEll : 0 < ell) :
    (daiLiKGeDResidualSubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected ⊆
      daiLiKGeDSeparator P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles := by
  intro q hq
  have hOutside : q ∉
      (daiLiKGeDASubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected ∪
      (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected :=
    (Finset.mem_sdiff.mp hq).2
  have hNotA : q ∉ (daiLiKGeDASubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected := by
    intro hA
    exact hOutside (Finset.mem_union_left _ hA)
  have hNotTrimmedB : q ∉ (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected := by
    intro hB
    exact hOutside (Finset.mem_union_right _ hB)
  have hCellCover : q ∈ (embedding.gridOccupiedCells w (gridOrigin w t)).biUnion
      (embedding.gridCellQubits w (gridOrigin w t)) := by
    rw [embedding.gridCellQubits_cover w (gridOrigin w t)]
    exact Finset.mem_univ _
  rcases Finset.mem_biUnion.mp hCellCover with ⟨cell, hCell, hqCell⟩
  rcases daiLiKGeD_cell_assignment P embedding d threshold w ell t atoms rectangles
      hAtoms hRectangles hw hEll cell hCell q hqCell with hSeparator | hA | hB
  · exact hSeparator
  · exact False.elim (hNotA hA)
  · exfalso
    apply hNotTrimmedB
    apply Finset.mem_sdiff.mpr
    exact ⟨hB, hNotA⟩
end QEC.Locality
