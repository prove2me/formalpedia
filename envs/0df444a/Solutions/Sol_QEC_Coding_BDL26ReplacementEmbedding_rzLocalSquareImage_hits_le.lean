-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rzLocalSquareImage_hits_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:40:42.698221+00:00
-- url     : https://prove2.me/submissions/6a9b69a9-202c-44d8-9cea-3a1347c74bdd

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
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzLocalFaceInclude_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (z : P.Z) (region : Set E) :
    (familyHits (rzLocalSquareImage P A S J z) region).card ≤
      (familyHits (rzFaceImage P A S J) region).card :=
  familyHits_restrict_card_le _ (rzLocalFaceInclude_injective P S z) _ _
end QEC.Coding.BDL26ReplacementEmbedding
