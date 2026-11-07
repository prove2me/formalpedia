-- Prove2me | solution 1 for QEC.Locality.card_daiLiGridSideStrip_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:15:59.590892+00:00
-- url     : https://prove2.me/submissions/58b74ff6-2e7c-4e43-8cfe-58b473afb473

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_card_qubitsInRectangle_le_six_mul_area


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
    (embedding : UnitSeparatedEmbedding2D ι) (w edgeRadius vertexRadius : ℝ)
    (origin : ℝ × ℝ) (side : DaiLiGridSideIndex)
    (hEdge : 1 ≤ 2 * edgeRadius) (hLong : 1 ≤ w - 2 * vertexRadius) :
    ((daiLiGridSideStripQubits embedding w edgeRadius vertexRadius origin side).card : ℝ) ≤
      12 * edgeRadius * (w - 2 * vertexRadius) := by
  by_cases hVertical : side.2.2
  · rw [daiLiGridSideStripQubits, if_pos hVertical]
    have h := embedding.card_qubitsInRectangle_le_six_mul_area
      (origin.1 + (side.1 : ℝ) * w - edgeRadius,
        origin.2 + (side.2.1 : ℝ) * w + vertexRadius)
      (origin.1 + (side.1 : ℝ) * w + edgeRadius,
        origin.2 + ((side.2.1 : ℝ) + 1) * w - vertexRadius)
      (by linarith) (by linarith)
    calc
      _ ≤ 6 * ((2 * edgeRadius) * (w - 2 * vertexRadius)) := by
        convert h using 1 <;> norm_num <;> ring
      _ = _ := by ring
  · rw [daiLiGridSideStripQubits, if_neg hVertical]
    have h := embedding.card_qubitsInRectangle_le_six_mul_area
      (origin.1 + (side.1 : ℝ) * w + vertexRadius,
        origin.2 + (side.2.1 : ℝ) * w - edgeRadius)
      (origin.1 + ((side.1 : ℝ) + 1) * w - vertexRadius,
        origin.2 + (side.2.1 : ℝ) * w + edgeRadius)
      (by linarith) (by linarith)
    calc
      _ ≤ 6 * ((w - 2 * vertexRadius) * (2 * edgeRadius)) := by
        convert h using 1 <;> norm_num <;> ring
      _ = _ := by ring
end QEC.Locality
