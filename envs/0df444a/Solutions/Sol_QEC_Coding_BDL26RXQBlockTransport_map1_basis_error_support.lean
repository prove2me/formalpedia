-- Prove2me | solution 1 for QEC.Coding.BDL26RXQBlockTransport.map1_basis_error_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:01:18.844197+00:00
-- url     : https://prove2.me/submissions/1626a025-a2c4-4fc1-b44f-cd293bd0c7f7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_basis_supported
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
theorem _root_.solution (q : QCoord S i) (a : Upper S depth i) :
    hammingSupport (a+(a+((indexedDecoderData S depth).selectedMap i).map1
      (canonicalBasisWord q))) ⊆ (rxLq S depth i h).correctionRegion q := by
  rw [← add_assoc, word_add_self, zero_add]
  exact map1_basis_supported S depth i h q
end QEC.Coding.BDL26RXQBlockTransport
