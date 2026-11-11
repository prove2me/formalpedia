-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rxLocalSquareImage_hits_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:40:03.821666+00:00
-- url     : https://prove2.me/submissions/c0f032ab-4baa-4249-9c99-c914ce21f3e5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_familyHits_restrict_card_le
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxLocalFaceInclude_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (region : Set E) :
    (familyHits (rxLocalSquareImage P S J x) region).card ≤
      (familyHits (rxFaceImage P S J) region).card :=
  familyHits_restrict_card_le _ (rxLocalFaceInclude_injective P S x) _ _
end QEC.Coding.BDL26ReplacementEmbedding
