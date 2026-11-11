-- Prove2me | solution 1 for QEC.Coding.BDL26RXQBlockTransport.rootCoefficient_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:41:21.847128+00:00
-- url     : https://prove2.me/submissions/204e1454-4ef7-45b5-be23-eac62da6d277

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_updated_self

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
theorem _root_.solution (q : QCoord S i) (a : Upper S depth i) :
    rootCoefficient S depth i h q a a=0 := by
  rw [rootCoefficient, updated_self]
  rfl
end QEC.Coding.BDL26RXQBlockTransport
