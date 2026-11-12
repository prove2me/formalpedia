-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rz_local_edge_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:56:34.013204+00:00
-- url     : https://prove2.me/submissions/9721f51d-3a1a-45b0-be74-bf83b92c0147

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
    (S : OddScale) (J : Vertex P → E) (z : P.Z) (e : ZDoubleCylinderEdge P z S) :
    rzVertexPoint P A S J (.q (.inl ⟨z, e⟩)) = (1 / 2 : ℝ) •
      (rzIntrinsicPoint P S J (.z z)
        (tannerDoubleCylinderEdgeStart (transposePresentation P) z S e) +
       rzIntrinsicPoint P S J (.z z)
        (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S e)) := rfl
end QEC.Coding.BDL26ReplacementEmbedding
