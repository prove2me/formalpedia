-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.incomingFaceGeometry_of_source_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:26:20.009415+00:00
-- url     : https://prove2.me/submissions/d6869fda-5835-4a30-9b86-cae9e3e5a6b8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {L lower width : ℝ} (hL : L ≤ S.ell)
    (hsideLo : ∀ f side, lower ≤ ‖J (.q (P.faceQ f side)) - J (.x (P.faceX f))‖)
    (hdiagLo : ∀ f, lower ≤ ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖)
    (hoppLo : ∀ f side, lower ≤ ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f side))‖)
    (hsideUp : ∀ f side, ‖J (.q (P.faceQ f side)) - J (.x (P.faceX f))‖ ≤ L)
    (hdiagUp : ∀ f, ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ L)
    (hoppUp : ∀ f side, ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f side))‖ ≤ L)
    (hthin : ∀ f side, TriangleWidthAtLeast
      (J (.q (P.faceQ f side)) - J (.x (P.faceX f)))
      (J (.z (P.faceZ f)) - J (.x (P.faceX f))) width) :
    IncomingFaceGeometry P S J lower width :=
  ⟨hsideLo, hdiagLo, hoppLo, fun f side => (hsideUp f side).trans hL,
    fun f => (hdiagUp f).trans hL, fun f side => (hoppUp f side).trans hL, hthin⟩
end QEC.Coding.BDL26ReplacementEmbedding
