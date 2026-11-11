-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.phi_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:19:50.916606+00:00
-- url     : https://prove2.me/submissions/95b9eb15-b885-45aa-a193-97d07d3c4e7e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_support_of_zero_off
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_zero_off_support


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
theorem _root_.solution (X0 : Finset (XCoord S i)) (a b : Upper S depth i) :
    hammingSupport (Phi S depth i h X0 a b) ⊆ degreeZeroBlocks S depth i h X0 := by
  apply support_of_zero_off
  intro p hp
  rw [Phi,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply zero_off_support _ _ (potential_supported S depth i h x a b) p
  exact fun hm => hp (Finset.mem_biUnion.mpr ⟨x,hx,hm⟩)
end QEC.Coding.BDL26RXFiniteBlockTransport
