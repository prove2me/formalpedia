-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.xLocalStripDualEdge_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:52:30.866354+00:00
-- url     : https://prove2.me/submissions/ed685990-f383-4222-b642-b04b900ed510

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_lift_graphBoundary
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalStripDualEdge_coboundary

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (side : Two) :
    (wordLinearMapTranspose (doubleCylinderBoundary2 P x S)).comp
        (xLocalWordPush (xLocalStripDualEdge P x S face side)) =
      (xLocalWordPush (fun i : StripVertex S.half => Sum.inr
        (subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x face side) i))).comp
        (graphBoundary (stripStart S.half) (stripEnd S.half)) :=
  xLocal_lift_graphBoundary _ _ _ _ _ (xLocalStripDualEdge_coboundary P x S face side)
end QEC.Coding.BDL26RXLocalReplacement
