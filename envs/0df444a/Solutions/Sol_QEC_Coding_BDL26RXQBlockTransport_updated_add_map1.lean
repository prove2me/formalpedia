-- Prove2me | solution 1 for QEC.Coding.BDL26RXQBlockTransport.updated_add_map1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:01:13.00874+00:00
-- url     : https://prove2.me/submissions/6f62f7c0-918b-44b7-a440-5198fe51c8f8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_correction_add_map1_eq
section
noncomputable section
namespace QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
private theorem word_add_self {ι : Type*} (w : Word BDL26Field ι) : w+w=0 := by
  funext p
  exact CharTwo.add_self_eq_zero (w p)
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
end QEC.Coding.BDL26RXQBlockTransport
end
end

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
theorem _root_.solution (a : Upper S depth i) (w : Lower S depth i) :
    updated S depth i h a (a+((indexedDecoderData S depth).selectedMap i).map1 w) =
      ((indexedDecoderData S depth).selectedMap i).map1 w := by
  rw [updated, correction_add_map1_eq]
  calc
    _ = (a+a) + ((indexedDecoderData S depth).selectedMap i).map1 w +
        ((run S depth i h a).correction+(run S depth i h a).correction) := by abel
    _ = _ := by rw [word_add_self, word_add_self, zero_add, add_zero]
end QEC.Coding.BDL26RXQBlockTransport
