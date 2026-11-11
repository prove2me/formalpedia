-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.chart_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:21:30.579652+00:00
-- url     : https://prove2.me/submissions/59d34609-f0ac-4857-89bc-91c9592361ed

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxPhysical_incidence


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXPhysicalStarTransport
theorem _root_.solution (r : RX0 (state S i.val).presentation S)
    (p : RX1 (state S i.val).presentation S) :
    (state S (i.val+1)).presentation.xq (rxDegreeZeroEquiv S depth i h r)
      (upperQChart S depth i h p)=rxXQIncidence (state S i.val).presentation S r p := by
  exact rxPhysical_incidence S depth i h r p
end QEC.Coding.BDL26RXPhysicalStarTransport
