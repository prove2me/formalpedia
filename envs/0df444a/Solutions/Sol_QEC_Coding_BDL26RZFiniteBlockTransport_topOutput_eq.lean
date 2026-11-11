-- Prove2me | solution 1 for QEC.Coding.BDL26RZFiniteBlockTransport.topOutput_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:55:26.499548+00:00
-- url     : https://prove2.me/submissions/828b5f68-013c-43e4-a89e-6bf44c15990b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_outputAt_top
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)
open BDL26OwnerIncidenceMasks BDL26CanonicalHistoryMarks
namespace QEC.Coding.BDL26RZFiniteBlockTransport
theorem _root_.solution (j : Nat) (a : Upper S (2*j+4) (topStep j)) :
    topOutput S j a=run S (2*j+4) (topStep j) (topStep_odd j) a := by
  exact (BDL26CanonicalHistoryMarks.outputAt_top S (2*j+1)
    (errorSyndrome S (2*j+4) (topStep j) a)).trans
    (congrFun (actualStep_rz S (2*j+4) (topStep j) (topStep_odd j)) _)
end QEC.Coding.BDL26RZFiniteBlockTransport
