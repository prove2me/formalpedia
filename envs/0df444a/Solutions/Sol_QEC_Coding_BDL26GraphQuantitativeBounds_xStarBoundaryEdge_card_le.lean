-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.xStarBoundaryEdge_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:41:45.687346+00:00
-- url     : https://prove2.me/submissions/ea93218a-b612-4a0e-ae53-3ec4d960420f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_xStarEdge_card_le
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (P : TannerSquarePresentation) (h : BoundedValence P)
    (x : P.X) : Fintype.card (XStarBoundaryEdge P x) ≤ 56 :=
  (Fintype.card_le_of_injective _ (boundaryEdgeEmbedding P x).injective).trans
    (xStarEdge_card_le P h x)
end QEC.Coding.BDL26GraphQuantitativeBounds
