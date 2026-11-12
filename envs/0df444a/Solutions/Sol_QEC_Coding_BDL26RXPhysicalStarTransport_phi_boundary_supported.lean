-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.phi_boundary_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:25:18.440824+00:00
-- url     : https://prove2.me/submissions/af4a8421-5e69-4767-980a-e0fc198fccb1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_singleton
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_boundary_supported
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
    hammingSupport ((indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b)) ⊆
      star1 S depth i h (parentX S depth i h u) := by
  rw [Phi,BDL26RXFiniteBlockTransport.phi_singleton]
  exact potential_boundary_supported S depth i h _ a b
end QEC.Coding.BDL26RXPhysicalStarTransport
