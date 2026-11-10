-- Prove2me | solution 1 for QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_vertical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:10:53.738463+00:00
-- url     : https://prove2.me/submissions/02d1587f-4321-4964-8b4b-7f86f6139cd3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical
namespace QEC.Coding.BDL26XLocalConnectingWeight
theorem _root_.solution
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (q : Neighbor P x)
    (e : QStarEdge P q.val) :
    copiedQ P x S (outputEdge P A x S ⟨q, Sum.inr e⟩) = none := rfl
end QEC.Coding.BDL26XLocalConnectingWeight
