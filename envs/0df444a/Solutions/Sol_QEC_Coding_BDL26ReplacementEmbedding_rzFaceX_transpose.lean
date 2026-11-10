-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rzFaceX_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:35:01.454216+00:00
-- url     : https://prove2.me/submissions/422d12cf-07fc-440f-962c-71e31ae6ca8a

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
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (f : BDL26RZLocalReplacement.RZFace P S) :
    BDL26RZLocalReplacement.rzFaceX P S f =
      rxFaceZ (transposePresentation P) S (rzFaceEquiv P S f) := by
  rcases f with localFace | glue | old
  · rfl
  · rcases glue with ⟨⟨⟨q, z⟩, hqz⟩, edge, endpoint⟩
    rfl
  · rfl
end QEC.Coding.BDL26ReplacementEmbedding
