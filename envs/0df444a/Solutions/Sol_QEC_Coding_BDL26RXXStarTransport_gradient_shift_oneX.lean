-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.gradient_shift_oneX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:54:50.638634+00:00
-- url     : https://prove2.me/submissions/3729fdb9-cebe-45ee-b4ec-9f32356a3733

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradientError_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXXStarTransport
theorem _root_.solution (x : XCoord S i) (a : Upper S depth i) :
    OneX S depth i h x a (a+gradientError S depth i h x) := by
  change hammingSupport (a+(a+gradientError S depth i h x)) ⊆ _
  rw [← add_assoc,word_add_self,zero_add]
  exact gradientError_supported S depth i h x
end QEC.Coding.BDL26RXXStarTransport
