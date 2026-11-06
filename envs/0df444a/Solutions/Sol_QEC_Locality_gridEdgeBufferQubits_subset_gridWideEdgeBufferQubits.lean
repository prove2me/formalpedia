-- Prove2me | solution 1 for QEC.Locality.gridEdgeBufferQubits_subset_gridWideEdgeBufferQubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:19:18.535334+00:00
-- url     : https://prove2.me/submissions/9fc6fb33-dbd8-429b-b7b3-0807ea37e341

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition

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
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive
namespace QEC.Locality
theorem _root_.solution
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) (hell : 0 ≤ ell) :
    gridEdgeBufferQubits embedding w ell t ⊆
      gridWideEdgeBufferQubits embedding w ell t := by
  classical
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨_, hNotVertex, hEdge⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ q, hNotVertex, ?_⟩
  rcases hEdge with hEdge | hEdge
  · exact Or.inl (hEdge.trans (by linarith))
  · exact Or.inr (hEdge.trans (by linarith))
end QEC.Locality
