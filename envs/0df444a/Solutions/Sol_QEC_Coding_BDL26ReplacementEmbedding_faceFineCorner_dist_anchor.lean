-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.faceFineCorner_dist_anchor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:17:05.248889+00:00
-- url     : https://prove2.me/submissions/11ae1a37-2be8-47e2-af43-9be0f7a78b89

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedGridPoint_corner_dist

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (h₀ : ‖J (.q (P.faceQ f 0)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (h₁ : ‖J (.q (P.faceQ f 1)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz : ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz₀ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 0))‖ ≤ S.ell)
    (hz₁ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 1))‖ ≤ S.ell) :
    dist (faceFineCorner P S J f m n a b) (faceFineAnchor P S J f m n) ≤ 1 :=
  foldedGridPoint_corner_dist _ _ _ _
    (by exact_mod_cast (show 0 < S.ell by have := S.three_le; omega))
    m n a b h₀ h₁ hz hz₀ hz₁
end QEC.Coding.BDL26ReplacementEmbedding
