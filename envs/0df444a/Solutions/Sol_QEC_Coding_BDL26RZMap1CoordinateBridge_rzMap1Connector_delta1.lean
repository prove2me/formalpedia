-- Prove2me | solution 1 for QEC.Coding.BDL26RZMap1CoordinateBridge.rzMap1Connector_delta1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:18:13.981019+00:00
-- url     : https://prove2.me/submissions/70e518fe-a076-4313-bb6b-df362c0c5f40

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_graphBoundary_pathChain


set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZMap1CoordinateBridge
open scoped BigOperators
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
open BDL26RZLocalReplacement
open MultiscaleDecoder
attribute [local instance] QEC.Coding.BDL26RZMap1CoordinateBridge.rzQDecidableEq
attribute [local instance] rzQFintype
attribute [local instance] QEC.Coding.BDL26RZMap1CoordinateBridge.subdivisionEdgeDecidableEq
attribute [local instance] subdivisionEdgeDecidableEq
universe u
namespace QEC.Coding.BDL26RZMap1CoordinateBridge
theorem _root_.solution
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale) :
    rzCzGraphBoundary P z S (rzMap1Connector P A4 q z hqz S) =
      canonicalBasisWord (rzMap1ZRoot P A4 z S) +
        canonicalBasisWord
          (qToZDoubleCylinderVertex P A4.toTannerSquareAdmissible
            q z hqz S (rzMap1QRoot P q S)) := by
  classical
  exact graphBoundary_pathChain
    (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
    (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
    (rzMap1ZRoot P A4 z S)
    (rzMap1ConnectorPath P A4 q z hqz S)
end QEC.Coding.BDL26RZMap1CoordinateBridge
