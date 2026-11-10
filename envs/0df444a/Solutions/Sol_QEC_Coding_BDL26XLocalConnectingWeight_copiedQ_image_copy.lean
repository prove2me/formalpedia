-- Prove2me | solution 1 for QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_copy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:13:40.973548+00:00
-- url     : https://prove2.me/submissions/ada46380-1b44-49a9-bf5a-bd46b8360ca8

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
    copiedQ P x S (outputEdge P A x S ⟨q, Sum.inl e⟩) = some q.val := rfl
end QEC.Coding.BDL26XLocalConnectingWeight
