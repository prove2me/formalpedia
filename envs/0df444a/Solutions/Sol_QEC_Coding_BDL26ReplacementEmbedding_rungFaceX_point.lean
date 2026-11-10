-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rungFaceX_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:26:15.573699+00:00
-- url     : https://prove2.me/submissions/151f1ae2-d1ed-4cf7-a8d3-0ca93096f807

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
    (J : Vertex P → E) (a : XQEdge P) (edge : QStarEdge P a.1.2)
    (copy : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (glueFaceX P S ⟨a, .inr edge, copy⟩) =
      (1 - contractionRatio S) • J (.x a.1.1) + contractionRatio S • J (.z edge.1) := by
  fin_cases copy <;> rfl
end QEC.Coding.BDL26ReplacementEmbedding
