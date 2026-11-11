-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.eq_of_word_add_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:40:02.946213+00:00
-- url     : https://prove2.me/submissions/09fa9d12-7efc-4de6-8d6f-bfb1ccf1d0f6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution {ι : Type*} (u v : Word BDL26Field ι)
    (hh : u+v=0) : u=v := by
  have he := congrArg (fun t => u+t) hh
  rw [← add_assoc, word_add_self, zero_add, add_zero] at he
  exact he.symm
end QEC.Coding.BDL26RXXStarTransport
