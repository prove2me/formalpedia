-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rxQZ_edge_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:55:37.301703+00:00
-- url     : https://prove2.me/submissions/d59a78de-74bd-46ab-a2bb-c6e7b1b03033

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFace_boundaryUnit

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (q : RX1 P S) (z : RX2 P S) (hinc : rxQZIncidence P S q z = true) :
    dist (rxOnePoint P S J q) (rxTwoPoint P S J z) ≤ 1 := by
  obtain ⟨f, side, rfl, rfl⟩ := (rxQZIncidence_eq_true_iff P S q z).mp hinc
  have h := rxFace_boundaryUnit P S J hgeo f
  fin_cases side
  · exact h.2.2.1
  · exact h.2.2.2
end QEC.Coding.BDL26ReplacementEmbedding
