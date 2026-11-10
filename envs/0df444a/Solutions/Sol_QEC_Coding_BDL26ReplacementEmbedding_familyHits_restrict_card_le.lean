-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.familyHits_restrict_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:42:58.921022+00:00
-- url     : https://prove2.me/submissions/fe685205-d67b-4b42-a4bf-9abdb26b72bf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution {A B : Type*} [Fintype A] [Fintype B]
    (embed : A → B) (hinj : Function.Injective embed) (images : B → Set E) (region : Set E) :
    (familyHits (images ∘ embed) region).card ≤ (familyHits images region).card := by
  classical
  apply Finset.card_le_card_of_injOn embed
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  · intro a ha b hb h
    exact hinj h
end QEC.Coding.BDL26ReplacementEmbedding
