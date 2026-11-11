-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.lower_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:42:11.660573+00:00
-- url     : https://prove2.me/submissions/dc60858b-950d-4089-bceb-193377fa59b4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_mem_starQ
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_support_of_zero_off
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_zero_off_support
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.mem_starQ



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
theorem _root_.solution (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    hammingSupport (lowerWord S depth i h x a b) ⊆ incidentQ S depth i x := by
  apply support_of_zero_off
  intro q hq
  apply zero_off_support _ _ (remainder_supported S depth i h x a b he)
  intro hp
  obtain ⟨r,hr,hpr⟩ := (mem_starQ S depth i h x _).mp hp
  have hrq : r=q := by
    by_contra hn
    exact (Finset.disjoint_left.mp
      ((rxData S depth i h).cq_correction_regions_pairwise_disjoint r q hn))
      hpr (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).property
  exact hq (hrq ▸ hr)
end QEC.Coding.BDL26RXXStarTransport
