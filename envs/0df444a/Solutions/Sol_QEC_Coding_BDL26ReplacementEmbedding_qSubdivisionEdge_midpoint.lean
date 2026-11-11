-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.qSubdivisionEdge_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:53:59.638784+00:00
-- url     : https://prove2.me/submissions/e40ec2fd-6fd4-42ef-9979-b68bba64390e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_qSubdivisionEdgeStart_point
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_qSubdivisionEdgeEnd_point

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (q : P.Q) (edge : QStarEdge P q) (i : Fin S.half) :
    (1 / 2 : ℝ) •
      (qSubdivisionVertexPoint P S J q (qSubdivisionEdgeStart P q S (edge, i)) +
       qSubdivisionVertexPoint P S J q (qSubdivisionEdgeEnd P q S (edge, i))) =
      (1 - (2 * (i.val : ℝ) + 1) / S.ell) • J (.q q) +
        ((2 * (i.val : ℝ) + 1) / S.ell) • J (.z edge.1) := by
  rw [qSubdivisionEdgeStart_point, qSubdivisionEdgeEnd_point]
  module
end QEC.Coding.BDL26ReplacementEmbedding
