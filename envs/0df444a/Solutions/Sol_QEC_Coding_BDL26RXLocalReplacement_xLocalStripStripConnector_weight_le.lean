-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.xLocalStripStripConnector_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:55:21.609705+00:00
-- url     : https://prove2.me/submissions/b8b9bb2e-6132-4939-bf8d-485ff528f8e2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_connectingWeight_single_le_of_vertical


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (b : Field) :
    connectingWeight P A x S (Pi.single (xLocalStripStripConnector P x S face) b) ≤
      2 * bitWeight b :=
  connectingWeight_single_le_of_vertical P A R x S _ (P.faceZ face.val) rfl b
end QEC.Coding.BDL26RXLocalReplacement
