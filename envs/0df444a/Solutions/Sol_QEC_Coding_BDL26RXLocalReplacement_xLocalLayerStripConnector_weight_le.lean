-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.xLocalLayerStripConnector_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:55:18.939717+00:00
-- url     : https://prove2.me/submissions/776f87fc-d6a8-4caf-9932-21aba07a6c21

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_connectingWeight_single_le_of_copied


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (copy side : Two) (b : Field) :
    connectingWeight P A x S (Pi.single (xLocalLayerStripConnector P x S face copy side) b) ≤
      bitWeight b :=
  connectingWeight_single_le_of_copied P A x S _ (P.faceQ face.val side) rfl b
end QEC.Coding.BDL26RXLocalReplacement
