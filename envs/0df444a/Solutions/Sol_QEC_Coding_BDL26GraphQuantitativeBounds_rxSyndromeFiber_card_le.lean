-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.rxSyndromeFiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:53:06.466621+00:00
-- url     : https://prove2.me/submissions/ee1e9cb7-57f5-4fe7-8b62-4e6a7113a4fe

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rxSyndromeCell_card_le
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rxSyndromeCellToFiber_surjective
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
open BDL26ReplacementSupport
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (P : TannerSquarePresentation) (h : BoundedValence P)
    (S : OddScale) (u : Vertex P) :
    Fintype.card {c : RX2 P S // rxSyndromeOwner P S c = u} ≤ localCoordinateBound S :=
  (Fintype.card_le_of_surjective _ (rxSyndromeCellToFiber_surjective P S u)).trans
    (rxSyndromeCell_card_le P h S u)
end QEC.Coding.BDL26GraphQuantitativeBounds
