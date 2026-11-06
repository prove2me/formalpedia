-- Prove2me | solution 2 for QEC.Locality.gridEdgeBufferQubits_subset_gridWideEdgeBufferQubits
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:29:57.40427+00:00
-- url     : https://prove2.me/submissions/4d5d32dd-1ec9-4c45-93d8-0564be9e15b6

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

theorem solution
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) (hell : 0 ≤ ell) :
    gridEdgeBufferQubits embedding w ell t ⊆
      gridWideEdgeBufferQubits embedding w ell t := by
  intro q hq
  simp only [gridEdgeBufferQubits, gridWideEdgeBufferQubits, Finset.mem_filter] at hq ⊢
  refine ⟨hq.1, hq.2.1, ?_⟩
  have h := hq.2.2
  unfold edgeBad at h ⊢
  rcases h with h | h
  · left; linarith
  · right; linarith
