-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.phi_boundary_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:28:09.33689+00:00
-- url     : https://prove2.me/submissions/076441bd-818c-45ef-9721-472ff140d986

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_mem_starQ
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_boundary_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_support_of_zero_off
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_zero_off_support
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.mem_starQ



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
    (a b : Upper S depth i) :
    hammingSupport ((indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b)) ⊆
      star S depth i h X0 Q0 := by
  apply support_of_zero_off
  intro p hp
  rw [Phi,map_sum,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply zero_off_support _ _ (potential_boundary_supported S depth i h x a b) p
  intro hm
  rcases Finset.mem_union.mp hm with hpx | hpq
  · exact hp (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨x,hx,hpx⟩))
  · obtain ⟨q,hq,hpq⟩ := (mem_starQ S depth i h x p).mp hpq
    exact hp (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨q,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,hx,hq⟩),hpq⟩))
end QEC.Coding.BDL26RXFiniteBlockTransport
