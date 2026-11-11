-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.pathStripFaceZ_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:58:29.922364+00:00
-- url     : https://prove2.me/submissions/3d466232-ad7b-4ebb-98f7-b95d820cc794

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_qSubdivisionEdge_midpoint

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (side copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (endpoint : BDL26FiniteTannerSquare.Two) :
    rxTwoPoint P S J (rxFaceZ P S (pathStripFace P S f side copy i endpoint)) =
      (1 - (2 * (i.val : ℝ) + 1) / S.ell) • J (.q (P.faceQ f side)) +
        ((2 * (i.val : ℝ) + 1) / S.ell) • J (.z (P.faceZ f)) :=
  qSubdivisionEdge_midpoint P S J (P.faceQ f side)
    ⟨P.faceZ f, P.data.faceQ_qz f side⟩ i
end QEC.Coding.BDL26ReplacementEmbedding
