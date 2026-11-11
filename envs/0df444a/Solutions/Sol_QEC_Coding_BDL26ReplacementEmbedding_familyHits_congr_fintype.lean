-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.familyHits_congr_fintype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:34:27.308321+00:00
-- url     : https://prove2.me/submissions/b60b07f8-5e70-4904-8c5b-a592022ff210

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
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution {ι D : Type*} (I₁ I₂ : Fintype ι)
    (images₁ images₂ : ι → Set D) (he : ∀ i, images₁ i = images₂ i) (region : Set D) :
    @familyHits ι D I₁ images₁ region = @familyHits ι D I₂ images₂ region := by
  have hI : I₁ = I₂ := Subsingleton.elim _ _
  have himages : images₁ = images₂ := funext he
  subst I₂
  subst images₂
  rfl
end QEC.Coding.BDL26ReplacementEmbedding
