-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.remainder_x_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:36:56.565224+00:00
-- url     : https://prove2.me/submissions/d9b60b59-5f98-4a21-a7ec-deedc61191ab

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_boundary_x
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_boundary_other_x
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_updated_other_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_updated_other_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXFiniteBlockTransport
theorem _root_.solution (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (y : XCoord S i) (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) (R S depth i h X0 a b)=0 := by
  rw [R,map_add]
  by_cases hy : y ∈ X0
  · rw [phi_boundary_x S depth i h X0 y hy,word_add_self]
  · rw [updated_other_x_zero S depth i h X0 Q0 y hy a b he,
      phi_boundary_other_x S depth i h X0 y hy,zero_add]
end QEC.Coding.BDL26RXFiniteBlockTransport
