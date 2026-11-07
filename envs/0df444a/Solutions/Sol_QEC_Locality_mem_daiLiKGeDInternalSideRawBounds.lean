-- Prove2me | solution 1 for QEC.Locality.mem_daiLiKGeDInternalSideRawBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:15:48.595746+00:00
-- url     : https://prove2.me/submissions/193a3caf-a9b9-479b-b24d-9952db7c3f3b

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff



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
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiKGeDInternalSideIndex) (q : ι)
    (hq : q ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).1
      (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).2 3) :
    (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).1.1 + 2 * ell ≤
        (embedding.point q).1 ∧
      (embedding.point q).1 ≤
        (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).2.1 - 2 * ell ∧
      (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).2.2 - ell ≤
        (embedding.point q).2 ∧
      (embedding.point q).2 ≤
        (daiLiKGeDInternalSideRectangle embedding w origin rectangles side).2.2 + ell := by
  rw [daiLiRectangleSideStripQubits,
    UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff] at hq
  refine ⟨hq.1.1, hq.1.2, ?_, hq.2.2⟩
  linarith [hq.2.1]
end QEC.Locality
