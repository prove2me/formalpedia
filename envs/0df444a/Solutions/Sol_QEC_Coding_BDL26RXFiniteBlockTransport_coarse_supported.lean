-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.coarse_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:54:50.155802+00:00
-- url     : https://prove2.me/submissions/723b58ba-340e-4354-be84-4d6aa120498a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_coarse_apply
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_coarse_apply
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_support_of_zero_off


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
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    hammingSupport (coarseSum S depth i h a b).val ⊆ neighborZ S depth i X0 Q0 := by
  apply support_of_zero_off
  intro z hz
  rw [coarse_apply S depth i h X0 Q0 a b he z]
  apply Finset.sum_eq_zero
  intro q hq
  have hqz : (state S i.val).presentation.qz q z ≠ true := by
    intro hh
    exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨q,hq,hh⟩⟩)
  rw [if_neg hqz,mul_zero]
end QEC.Coding.BDL26RXFiniteBlockTransport
