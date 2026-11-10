-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.xCylinder_boundary_eq_cycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:23:56.996194+00:00
-- url     : https://prove2.me/submissions/02156faf-8bee-4c9c-8520-d50dd9934e5e

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_xCylinder_coboundary_eq_cocycle
import Theorems.Thm_QEC_Coding_LinearCode_dual_dual_carrier_eq
import Theorems.Thm_QEC_Coding_LinearCode_eq_of_carrier_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph
namespace QEC.Coding.BDL26LevelTwoDistance
theorem _root_.solution (P : TannerSquarePresentation)
    (A3 : TannerSquareAdmissibleV3 P) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) :
    (rxCx P x S).middleBoundaryCode.carrier =
      (rxCx P x S).middleCycleCode.carrier := by
  have hcode : (rxCx P x S).firstCoboundaryCheckCode =
      (rxCx P x S).middleCocycleCode :=
    LinearCode.eq_of_carrier_eq (xCylinder_coboundary_eq_cocycle P A3 R x S)
  have hdual : (rxCx P x S).middleBoundaryCode.dual =
      (rxCx P x S).middleCocycleCode :=
    LinearCode.eq_of_carrier_eq
      (rxCx P x S).middleBoundaryCode_dual_carrier_eq_middleCocycleCode
  rw [← ChainComplexData.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode,
    hcode, ← hdual, LinearCode.dual_dual_carrier_eq]
end QEC.Coding.BDL26LevelTwoDistance
