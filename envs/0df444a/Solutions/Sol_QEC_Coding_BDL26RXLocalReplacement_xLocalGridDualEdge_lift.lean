-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.xLocalGridDualEdge_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:56:40.625172+00:00
-- url     : https://prove2.me/submissions/e19d142d-1d74-403f-b83d-79d956f5ee9c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_lift_graphBoundary
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalGridDualEdge_coboundary

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (copy : Two) :
    (wordLinearMapTranspose (doubleCylinderBoundary2 P x S)).comp
        (xLocalWordPush (xLocalGridDualEdge P x S face copy)) =
      (xLocalWordPush (fun ij : GridVertex S.half => Sum.inl (copy, face, ij))).comp
        (graphBoundary (gridStart S.half) (gridEnd S.half)) :=
  xLocal_lift_graphBoundary _ _ _ _ _ (xLocalGridDualEdge_coboundary P x S face copy)
end QEC.Coding.BDL26RXLocalReplacement
