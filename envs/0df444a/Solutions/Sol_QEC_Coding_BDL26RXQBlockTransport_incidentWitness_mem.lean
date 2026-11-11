-- Prove2me | solution 1 for QEC.Coding.BDL26RXQBlockTransport.incidentWitness_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:35:46.776094+00:00
-- url     : https://prove2.me/submissions/4b0c1265-5672-43f1-8dac-65475ff2f963

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXQBlockTransport
theorem _root_.solution (S : OddScale) {depth : Nat} (i : StepIndex depth)
    (q : QCoord S i) :
    (state S i.val).presentation.qz q (incidentWitness S i q)=true :=
  ((state S i.val).admissible.toTannerSquareAdmissible.qzRoot q).property
end QEC.Coding.BDL26RXQBlockTransport
