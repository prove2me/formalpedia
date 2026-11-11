-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.lower_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:01:29.604203+00:00
-- url     : https://prove2.me/submissions/aa112d46-a577-470b-a916-1355de28be51

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_supported
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
theorem _root_.solution (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    hammingSupport (L S depth i h X0 a b) ⊆ neighbors S depth i X0 Q0 := by
  apply support_of_zero_off
  intro q hq
  apply zero_off_support _ _ (remainder_supported S depth i h X0 Q0 a b he)
  intro hp
  obtain ⟨r,hr,hpr⟩ := Finset.mem_biUnion.mp hp
  have hrq : r=q := by
    by_contra hn
    exact (Finset.disjoint_left.mp
      ((rxData S depth i h).cq_correction_regions_pairwise_disjoint r q hn))
      hpr (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).property
  exact hq (hrq ▸ hr)
end QEC.Coding.BDL26RXFiniteBlockTransport
