-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rz_q_local_edge_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:49:12.305919+00:00
-- url     : https://prove2.me/submissions/11e6468d-3970-4176-94c5-d3241e9f7359

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
open BDL26DecodingGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (q : P.Q)
    (e : QDoubleCylinderEdge (transposePresentation P) q S) :
    rzVertexPoint P A S J (.x (.inl (.inr ⟨q, e⟩))) = (1 / 2 : ℝ) •
      (rzIntrinsicPoint P S J (.q q)
        (qDoubleCylinderEdgeStart (transposePresentation P) q S e) +
       rzIntrinsicPoint P S J (.q q)
        (qDoubleCylinderEdgeEnd (transposePresentation P) q S e)) := rfl
end QEC.Coding.BDL26ReplacementEmbedding
