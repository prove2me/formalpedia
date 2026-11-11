-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.phi_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:24:05.95427+00:00
-- url     : https://prove2.me/submissions/a10d600f-7af1-43b5-b91d-231accb9fbd9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_singleton
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_supported
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.phi_singleton



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXPhysicalStarTransport
theorem _root_.solution (u : FamilyX S depth i.succ) (a b : Upper S depth i) :
    hammingSupport (Phi S depth i h u a b) ⊆ degreeZeroBlock S depth i h (parentX S depth i h u) := by
  rw [Phi,BDL26RXFiniteBlockTransport.phi_singleton]
  exact potential_supported S depth i h _ a b
end QEC.Coding.BDL26RXPhysicalStarTransport
