-- Prove2me | solution 1 for QEC.Locality.gridCellQubits_subset_daiLiGridCellClosedQubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:12:00.004312+00:00
-- url     : https://prove2.me/submissions/56e6f98b-eecb-49d9-a79c-1cc904254ed3

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_daiLiGridCellClosedQubits_eq_rectangle
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_gridCellQubits_subset_qubitsInRectangle


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
    (embedding : UnitSeparatedEmbedding2D ι) {w : ℝ} (hw : 0 < w)
    (origin : ℝ × ℝ) (cell : ℤ × ℤ) :
    embedding.gridCellQubits w origin cell ⊆
      daiLiGridCellClosedQubits embedding w origin cell := by
  rw [daiLiGridCellClosedQubits_eq_rectangle]
  exact embedding.gridCellQubits_subset_qubitsInRectangle hw origin cell
end QEC.Locality
