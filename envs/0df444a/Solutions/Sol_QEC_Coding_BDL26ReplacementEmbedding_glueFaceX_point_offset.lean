-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.glueFaceX_point_offset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:58:05.852277+00:00
-- url     : https://prove2.me/submissions/35b66d9c-dc74-4dc9-b575-b46b8802feb2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_qToXSubdivisionVertexAtRoot_point

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QDoubleCylinderEdge P a.1.2 S)
    (endpoint : BDL26FiniteTannerSquare.Two) :
    rxZeroPoint P S J (glueFaceX P S ⟨a, edge, endpoint⟩) =
      (1 - contractionRatio S) • J (.x a.1.1) +
        rxOnePoint P S J (glueFaceQ1 P S ⟨a, edge, endpoint⟩) -
        (1 - contractionRatio S) • J (.q a.1.2) := by
  let root := qDoubleCylinderUnderlyingStarEdge P a.1.2 S edge
  fin_cases endpoint
  · change subdivisionVertexPoint P S J a.1.1
        (tannerDoubleCylinderEdgeStart P a.1.1 S
          (qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S edge)).2 = _
    rw [← qToXDoubleCylinderEdgeRaw_start P a.1.2 a.1.1 a.2 S root edge]
    exact qToXSubdivisionVertexAtRoot_point P S J a.1.2 a.1.1 a.2 root
      (qDoubleCylinderEdgeStart P a.1.2 S edge).2
  · change subdivisionVertexPoint P S J a.1.1
        (tannerDoubleCylinderEdgeEnd P a.1.1 S
          (qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S edge)).2 = _
    rw [← qToXDoubleCylinderEdgeRaw_end P a.1.2 a.1.1 a.2 S root edge]
    exact qToXSubdivisionVertexAtRoot_point P S J a.1.2 a.1.1 a.2 root
      (qDoubleCylinderEdgeEnd P a.1.2 S edge).2
end QEC.Coding.BDL26ReplacementEmbedding
