-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rxXQ_edge_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:55:20.43531+00:00
-- url     : https://prove2.me/submissions/bec0f111-4539-4ba5-b360-be45f7cd899b

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
    (x : RX0 P S) (q : RX1 P S) (hinc : rxXQIncidence P S x q = true) :
    dist (rxZeroPoint P S J x) (rxOnePoint P S J q) ≤ 1 := by
  obtain ⟨f, side, rfl, rfl⟩ := (rxXQIncidence_eq_true_iff P S x q).mp hinc
  have h := rxFace_boundaryUnit P S J hgeo f
  fin_cases side
  · exact h.1
  · exact h.2.1
end QEC.Coding.BDL26ReplacementEmbedding
