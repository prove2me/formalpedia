-- Prove2me | solution 1 for QEC.Locality.not_mem_daiLiKGeDSeparator_not_badRectangleVertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:25:22.123767+00:00
-- url     : https://prove2.me/submissions/d9f02b88-1b61-4bad-a425-9cf39ac61efd

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_daiLiVertexNeighborhoodQubits_subset_badGridRectangleVertexBuffer

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
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (q : ι) (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles)
    (cell : ℤ × ℤ) (hCell : cell ∈ cells) (slot : ℕ)
    (hSlot : slot < (rectangles cell).length) (vertex : Fin 4) :
    q ∉ daiLiVertexNeighborhoodQubits embedding ell
      (daiLiRectangleVertex ((rectangles cell).get ⟨slot, hSlot⟩) vertex) := by
  intro hVertex
  apply hNotSeparator
  apply Finset.mem_union_right
  exact daiLiVertexNeighborhoodQubits_subset_badGridRectangleVertexBuffer
    embedding ell cells rectangles cell hCell slot hSlot vertex hVertex
end QEC.Locality
