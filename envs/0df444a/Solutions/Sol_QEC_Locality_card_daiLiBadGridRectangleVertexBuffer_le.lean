-- Prove2me | solution 1 for QEC.Locality.card_daiLiBadGridRectangleVertexBuffer_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:17:53.090399+00:00
-- url     : https://prove2.me/submissions/a244c35d-2b98-46ae-9dd2-f74014d1f0ff

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_card_daiLiBadGridRectangleVertexIndex
import Theorems.Thm_QEC_Locality_card_daiLiVertexNeighborhoodQubits_le

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
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (hEll : 1 ≤ ell)
    (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) ≤
      384 * ell ^ 2 *
        ((∑ cell ∈ cells, (rectangles cell).length : Nat) : ℝ) := by
  have hUnion :
      (daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card ≤
        ∑ vertex : DaiLiBadGridRectangleVertexIndex cells rectangles,
          (daiLiVertexNeighborhoodQubits embedding ell
            (daiLiBadGridRectangleVertexPoint cells rectangles vertex)).card := by
    exact Finset.card_biUnion_le
  have hEach : ∀ vertex : DaiLiBadGridRectangleVertexIndex cells rectangles,
      ((daiLiVertexNeighborhoodQubits embedding ell
        (daiLiBadGridRectangleVertexPoint cells rectangles vertex)).card : ℝ) ≤
        96 * ell ^ 2 := by
    intro vertex
    exact card_daiLiVertexNeighborhoodQubits_le embedding ell hEll _
  have hUnionReal :
      ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) ≤
        ∑ vertex : DaiLiBadGridRectangleVertexIndex cells rectangles,
          ((daiLiVertexNeighborhoodQubits embedding ell
            (daiLiBadGridRectangleVertexPoint cells rectangles vertex)).card : ℝ) := by
    exact_mod_cast hUnion
  calc
    _ ≤ ∑ vertex : DaiLiBadGridRectangleVertexIndex cells rectangles,
        ((daiLiVertexNeighborhoodQubits embedding ell
          (daiLiBadGridRectangleVertexPoint cells rectangles vertex)).card : ℝ) := hUnionReal
    _ ≤ ∑ _vertex : DaiLiBadGridRectangleVertexIndex cells rectangles,
        96 * ell ^ 2 := by
      apply Finset.sum_le_sum
      intro vertex _
      exact hEach vertex
    _ = 96 * ell ^ 2 *
        Fintype.card (DaiLiBadGridRectangleVertexIndex cells rectangles) := by
      rw [Finset.sum_const, Finset.card_univ]
      ring
    _ = 384 * ell ^ 2 *
        ((∑ cell ∈ cells, (rectangles cell).length : Nat) : ℝ) := by
      rw [card_daiLiBadGridRectangleVertexIndex]
      norm_num
      ring
end QEC.Locality
