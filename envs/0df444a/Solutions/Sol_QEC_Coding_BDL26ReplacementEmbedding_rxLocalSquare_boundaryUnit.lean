-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementEmbedding.rxLocalSquare_boundaryUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:49:27.339191+00:00
-- url     : https://prove2.me/submissions/40b26ec0-2196-49fc-9a9b-495897f3fabc

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
    (x : P.X)
    (f : DoubleCylinderFace P x S × (BDL26FiniteTannerSquare.Two × BDL26FiniteTannerSquare.Two)) :
    rxFaceBoundaryUnit P S J (rxLocalFaceInclude P S x f) :=
  rxFace_boundaryUnit P S J hgeo _
end QEC.Coding.BDL26ReplacementEmbedding
