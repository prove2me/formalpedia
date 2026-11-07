-- Prove2me | solution 1 for QEC.Locality.daiLiFiniteGridVertexBuffer_subset_gridVertexBuffer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:25:15.396946+00:00
-- url     : https://prove2.me/submissions/7c098728-34ca-4b5e-9d3e-f1aa190291ae

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_daiLiVertexNeighborhood_subset_gridVertexBuffer

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
    (ell : ℝ) (origin : ℝ × ℝ) (t : GridTranslation w)
    (ht : phase w origin = t) :
    daiLiFiniteGridVertexBuffer embedding w ell origin ⊆
      gridVertexBufferQubits embedding w ell t := by
  intro q hq
  rcases Finset.mem_biUnion.mp hq with ⟨vertex, hvertex, hqVertex⟩
  exact daiLiVertexNeighborhood_subset_gridVertexBuffer embedding hw ell origin t ht
    vertex hqVertex
end QEC.Locality
