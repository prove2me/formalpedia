-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.incident_card_le_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:01:39.241516+00:00
-- url     : https://prove2.me/submissions/222ad0c8-f750-4df9-91f5-eaec673f08b2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_incident_card_eq_tannerDegree
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_state_tannerDegree_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXActiveErrorTransport
theorem _root_.solution (x : XCoord S i) : (incidentQ S depth i x).card ≤ 7 := by
  rw [incident_card_eq_tannerDegree]
  exact state_tannerDegree_le S i.val (.x x)
end QEC.Coding.BDL26RXActiveErrorTransport
