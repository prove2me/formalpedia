-- Prove2me | solution 1 for QEC.Locality.card_daiLiKGeDSeparator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:15:25.847584+00:00
-- url     : https://prove2.me/submissions/633b9819-306c-41e8-a352-855c86ae4d11

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_card_longInteractionEndpointQubits_le_sum_counter


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
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ((daiLiKGeDSeparator P embedding threshold w ell t cells rectangles).card : ℝ) ≤
      (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        (∑ q : ι, P.daiLiInteractionCounter embedding threshold q : Nat) +
          ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) := by
  have hUnion :
      (daiLiKGeDSeparator P embedding threshold w ell t cells rectangles).card ≤
        (gridVertexBufferQubits embedding w ell t).card +
          (longInteractionEndpointQubits P embedding threshold).card +
            (daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card := by
    unfold daiLiKGeDSeparator
    calc
      _ ≤ (gridVertexBufferQubits embedding w ell t ∪
          longInteractionEndpointQubits P embedding threshold).card +
            (daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card :=
        Finset.card_union_le _ _
      _ ≤ ((gridVertexBufferQubits embedding w ell t).card +
          (longInteractionEndpointQubits P embedding threshold).card) +
            (daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = _ := by omega
  have hEndpoints := card_longInteractionEndpointQubits_le_sum_counter
    P embedding threshold
  have hVertex :
      (gridVertexBufferQubits embedding w ell t).card =
        vertexBadCount w (2 * ell) embedding.point t := by
    rfl
  have hUnionReal :
      ((daiLiKGeDSeparator P embedding threshold w ell t cells rectangles).card : ℝ) ≤
        ((gridVertexBufferQubits embedding w ell t).card : ℝ) +
          ((longInteractionEndpointQubits P embedding threshold).card : ℝ) +
            ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) := by
    exact_mod_cast hUnion
  calc
    _ ≤ ((gridVertexBufferQubits embedding w ell t).card : ℝ) +
          ((longInteractionEndpointQubits P embedding threshold).card : ℝ) +
            ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) :=
      hUnionReal
    _ ≤ (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
          (∑ q : ι, P.daiLiInteractionCounter embedding threshold q : Nat) +
            ((daiLiBadGridRectangleVertexBuffer embedding ell cells rectangles).card : ℝ) := by
      have hEndpointsReal :
          ((longInteractionEndpointQubits P embedding threshold).card : ℝ) ≤
            ∑ q : ι, P.daiLiInteractionCounter embedding threshold q := by
        exact_mod_cast hEndpoints
      rw [hVertex]
      linarith
end QEC.Locality
