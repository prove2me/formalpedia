-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.incident_card_eq_tannerDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:51:40.002316+00:00
-- url     : https://prove2.me/submissions/a58b12cc-6573-42b9-bc6e-56ea2a3cb39f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_incident_card_eq_xDegree

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
theorem _root_.solution (x : XCoord S i) :
    (incidentQ S depth i x).card=tannerDegree (state S i.val).presentation (.x x) := by
  rw [incident_card_eq_xDegree,xDegree,tannerDegree,
    Fintype.card_congr (xNeighborEquiv (state S i.val).presentation x)]
end QEC.Coding.BDL26RXActiveErrorTransport
