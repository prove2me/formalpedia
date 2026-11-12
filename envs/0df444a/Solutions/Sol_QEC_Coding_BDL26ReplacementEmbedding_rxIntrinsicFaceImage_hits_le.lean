-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rxIntrinsicFaceImage_hits_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:49:30.68056+00:00
-- url     : https://prove2.me/submissions/9c000596-312c-475d-b71b-ce7998645eb1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxLocalSquareImage_hits_le
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_familyHits_group_card_le
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (region : Set E) :
    (familyHits (rxIntrinsicFaceImage P S J x) region).card ≤
      (familyHits (rxFaceImage P S J) region).card :=
  (familyHits_group_card_le (rxLocalSquareImage P S J x) region).trans
    (rxLocalSquareImage_hits_le P S J x region)
end QEC.Coding.BDL26ReplacementEmbedding
