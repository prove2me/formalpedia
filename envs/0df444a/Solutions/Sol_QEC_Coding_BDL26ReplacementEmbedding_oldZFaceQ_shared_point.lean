-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.oldZFaceQ_shared_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:45:51.07279+00:00
-- url     : https://prove2.me/submissions/3a720546-b2b7-4310-a508-adc1f386e5b4

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
    (J : Vertex P → E) (f g : P.Face)
    (a b copy : BDL26FiniteTannerSquare.Two)
    (hq : P.faceQ f a = P.faceQ g b) (hz : P.faceZ f = P.faceZ g) :
    rxOnePoint P S J (oldZFaceQ P S a (f, copy)) =
      rxOnePoint P S J (oldZFaceQ P S b (g, copy)) :=
  congrArg (rxOnePoint P S J) (oldZFaceQ_congr P S f g a b copy hq hz)
end QEC.Coding.BDL26ReplacementEmbedding
