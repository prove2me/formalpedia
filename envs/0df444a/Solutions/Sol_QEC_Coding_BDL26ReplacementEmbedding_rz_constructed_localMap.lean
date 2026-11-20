-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rz_constructed_localMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:40:10.622165+00:00
-- url     : https://prove2.me/submissions/50c8949d-38fe-4c53-b6fc-238ae77f62cc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualRZHits_card_le
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzXQ_edge_dist
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzQZ_edge_dist
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzVertexPoint_hits

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26ReplacementEmbedding
theorem _root_.solution (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (J : Vertex P → E)
    {lower width tPrime : ℝ} (hlower : 0 < lower) (hwidth : 0 < width)
    (hgeo : IncomingFaceGeometry P S J lower width)
    (hincoming : ∀ center,
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    IsBoundedDensityLocalMap
      (BDL26RZLocalReplacement.rzReplacementPresentation P A4.toTannerSquareAdmissible S)
      (rzVertexPoint P A4.toTannerSquareAdmissible S J)
      (48 * Real.pi * tPrime * S.ell ^ 2 / (lower * width)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x q h
    exact rzXQ_edge_dist P A4 R S J hgeo x q h
  · intro q z h
    exact rzQZ_edge_dist P A4 R S J hgeo q z h
  · intro center
    rw [rzVertexPoint_hits]
    exact actualRZHits_card_le P A4.toTannerSquareAdmissible S J hlower hwidth hgeo center (hincoming center)
end QEC.Coding.BDL26ReplacementEmbedding
