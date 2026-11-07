-- Prove2me | solution 1 for QEC.Locality.daiLiFiniteGridSideBuffer_subset_gridEdgeBuffer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:25:16.687715+00:00
-- url     : https://prove2.me/submissions/2f7bb549-5024-4826-9c23-90d16eca6cc6

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_daiLiGridSideStrip_subset_gridEdgeBuffer

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
    (edgeRadius vertexRadius : ℝ) (origin : ℝ × ℝ) (t : GridTranslation w)
    (ht : phase w origin = t) :
    daiLiFiniteGridSideBuffer embedding w edgeRadius vertexRadius origin ⊆
      Finset.univ.filter fun q => edgeBad w edgeRadius t (embedding.point q) := by
  intro q hq
  rcases Finset.mem_biUnion.mp hq with ⟨side, hside, hqSide⟩
  exact daiLiGridSideStrip_subset_gridEdgeBuffer embedding hw edgeRadius vertexRadius
    origin t ht side hqSide
end QEC.Locality
