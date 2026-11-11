-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.actualPositive_hit_incoming
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:34:46.018907+00:00
-- url     : https://prove2.me/submissions/90042866-97f2-4126-a2be-6b4ea2961cf8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualFlatImage_raw_positive
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_fineEndpointBit_eq_of_coordinate_eq
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_fineQuadrantImage_hit_incoming
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rawPositiveFace_image_fine

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : PositiveCell S) (region : Set E)
    (hhit : (actualFlatImage P S J (f, .inl c) ∩ region).Nonempty) :
    (c.2.2.val ≤ c.2.1.val ∧ (oldTriangleImage P J (f, 0) ∩ region).Nonempty) ∨
      (c.2.1.val ≤ c.2.2.val ∧ (oldTriangleImage P J (f, 1) ∩ region).Nonempty) := by
  obtain ⟨raw, rfl⟩ := (rawPositiveCellEquiv S).surjective c
  rw [actualFlatImage_raw_positive, rawPositiveFace_image_fine] at hhit
  have hm := (fineCoordinateEquiv S raw.2.1).isLt
  have hn := (fineCoordinateEquiv S raw.2.2).isLt
  have h := fineQuadrantImage_hit_incoming P S J f
    (rawFineInteger S raw.2.1) (rawFineInteger S raw.2.2)
    (fineEndpointBit S raw.2.1) (fineEndpointBit S raw.2.2)
    (by unfold rawFineInteger; omega) (by unfold rawFineInteger; omega)
    (by unfold rawFineInteger; omega) (by unfold rawFineInteger; omega)
    (fineEndpointBit_eq_of_coordinate_eq S _ _) region hhit
  rcases h with ⟨hchart, hhit⟩ | ⟨hchart, hhit⟩
  · have hc : (fineCoordinateEquiv S raw.2.2).val ≤ (fineCoordinateEquiv S raw.2.1).val := by
      unfold rawFineInteger at hchart
      exact_mod_cast hchart
    exact .inl ⟨hc, hhit⟩
  · have hc : (fineCoordinateEquiv S raw.2.1).val ≤ (fineCoordinateEquiv S raw.2.2).val := by
      unfold rawFineInteger at hchart
      exact_mod_cast hchart
    exact .inr ⟨hc, hhit⟩
end QEC.Coding.BDL26ReplacementEmbedding
