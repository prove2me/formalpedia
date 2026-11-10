-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.rxParentFiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:45:25.868534+00:00
-- url     : https://prove2.me/submissions/7c52f3a3-9672-43bb-8313-eacdcedfd829

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rxParentFiber_card_le
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rxZeroCell_card_le
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (h : BoundedValence P) (S : OddScale) (u : Vertex P) :
    Fintype.card {v : Vertex (rxReplacementPresentation P S) //
      rxParent P S v = some u} ≤ localCoordinateBound S :=
  (rxParentFiber_card_le P S u).trans (rxZeroCell_card_le P A h S u)
end QEC.Coding.BDL26GraphQuantitativeBounds
