-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.full_gauge_x_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:54:54.069115+00:00
-- url     : https://prove2.me/submissions/36d1fd3a-93b0-4146-9661-ab22a79759e1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_lift_sum_restriction


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open BDL26RXStagedRestriction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCohomology
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (w : Word Field (RX1 P S))
    (f : ∀ x : P.X, Word Field (DoubleCylinderVertex P x S))
    (hf : ∀ x, wordLinearMapTranspose (localCx P S x).boundary1 (f x) =
      restrictWordLinear ((localX P S).correctionRegion x) w) :
    ∀ x, restrictWordLinear ((localX P S).correctionRegion x)
      (w - rxCoboundary0 P S (∑ y : P.X, xLift P S y (f y))) = 0 := by
  intro x
  rw [map_sub, localCx_lift_sum_restriction, hf, sub_self]
end QEC.Coding.BDL26RXCohomology
