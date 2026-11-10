-- Prove2me | solution 1 for QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_copy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:13:54.361207+00:00
-- url     : https://prove2.me/submissions/bb166300-359a-470d-8c28-0549b83fe608

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
    (e : Two × QSubdivisionEdge P q.val S) :
    verticalZ P x S (outputEdge P A x S ⟨q, Sum.inl e⟩) = none := rfl
end QEC.Coding.BDL26XLocalConnectingWeight
