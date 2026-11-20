-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.actualFlatHits_card_le_three_mul_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:10:06.927735+00:00
-- url     : https://prove2.me/submissions/490c9346-03b2-4701-8bad-706e3f51ae86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualFlatImage_subset_charge
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_familyHits_card_le_three_mul_positive


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (region : Set E) :
    (familyHits (actualFlatImage P S J) region).card ≤
      3 * (familyHits (fun p : P.Face × PositiveCell S =>
        actualFlatImage P S J (p.1, .inl p.2)) region).card :=
  familyHits_card_le_three_mul_positive S (actualFlatImage P S J) region
    (actualFlatImage_subset_charge P S J)
end QEC.Coding.BDL26ReplacementEmbedding
