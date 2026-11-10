-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_planar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:35:00.822211+00:00
-- url     : https://prove2.me/submissions/7faee913-c397-4e0a-92d8-d370f6111549

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
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (i j : Fin S.half) (copy a b : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (.inl ⟨P.faceX f, .inl (copy, oldFaceInXStar P f, i, j), a, b⟩) =
      (f, .inl (.inl ((copy, i, j), a, b))) := rfl
end QEC.Coding.BDL26ReplacementEmbedding
