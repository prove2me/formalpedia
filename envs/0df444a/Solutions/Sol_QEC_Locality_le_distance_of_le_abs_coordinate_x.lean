-- Prove2me | solution 1 for QEC.Locality.le_distance_of_le_abs_coordinate_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:10:04.753464+00:00
-- url     : https://prove2.me/submissions/14486eaf-9b54-48a4-a395-313fb38d4de5

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    (embedding : UnitSeparatedEmbedding2D ι) {p q : ι} {r : ℝ}
    (h : r ≤ |(embedding.point p).1 - (embedding.point q).1|) :
    r ≤ embedding.distance p q := by
  rw [UnitSeparatedEmbedding2D.distance, euclideanDistance2D]
  have hSq : ((embedding.point p).1 - (embedding.point q).1) ^ 2 ≤
      ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
        ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by
    nlinarith [sq_nonneg ((embedding.point p).2 - (embedding.point q).2)]
  exact h.trans (Real.abs_le_sqrt hSq)
end QEC.Locality
