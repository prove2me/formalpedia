-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.fineQuadrantImage_hit_incoming
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:25:49.666015+00:00
-- url     : https://prove2.me/submissions/79f0617a-164e-42d6-8739-f343067457b6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_fineQuadrantImage_subset_lower
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_fineQuadrantImage_subset_upper
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_fineQuadrantImage_diagonal_subset

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (hm0 : 0 ≤ m) (hn0 : 0 ≤ n) (hm1 : m + 1 ≤ (S.ell : ℤ))
    (hn1 : n + 1 ≤ (S.ell : ℤ)) (hdiag : m = n → a = b) (region : Set E)
    (hhit : (fineQuadrantImage P S J f m n a b ∩ region).Nonempty) :
    ((n ≤ m) ∧ (oldTriangleImage P J (f, 0) ∩ region).Nonempty) ∨
      ((m ≤ n) ∧ (oldTriangleImage P J (f, 1) ∩ region).Nonempty) := by
  obtain ⟨w, hw, hr⟩ := hhit
  rcases lt_trichotomy m n with hmn | he | hnm
  · exact .inr ⟨hmn.le, w,
      fineQuadrantImage_subset_upper P S J f m n a b hn1 hm0 (by omega) hw, hr⟩
  · subst n
    have hab := hdiag rfl
    subst b
    rcases fineQuadrantImage_diagonal_subset P S J f m a hm0 hm1 hw with h | h
    · exact .inl ⟨le_rfl, w, h, hr⟩
    · exact .inr ⟨le_rfl, w, h, hr⟩
  · exact .inl ⟨hnm.le, w,
      fineQuadrantImage_subset_lower P S J f m n a b hm1 hn0 (by omega) hw, hr⟩
end QEC.Coding.BDL26ReplacementEmbedding
