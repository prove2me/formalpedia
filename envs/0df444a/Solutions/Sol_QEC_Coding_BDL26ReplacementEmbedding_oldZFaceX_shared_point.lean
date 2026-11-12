-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.oldZFaceX_shared_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:45:37.361421+00:00
-- url     : https://prove2.me/submissions/12735391-074b-4b37-ad13-7fd756576dfc

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
    (J : Vertex P → E) (f g : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (hx : P.faceX f = P.faceX g) (hz : P.faceZ f = P.faceZ g) :
    rxZeroPoint P S J (oldZFaceX P S (f, copy)) =
      rxZeroPoint P S J (oldZFaceX P S (g, copy)) :=
  congrArg (rxZeroPoint P S J) (oldZFaceX_congr P S f g copy hx hz)
end QEC.Coding.BDL26ReplacementEmbedding
