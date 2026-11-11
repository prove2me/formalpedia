-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.input_supported_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:57:14.683783+00:00
-- url     : https://prove2.me/submissions/b12273a1-09c8-419d-b155-92ba8ed9ae1e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport

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
    hammingSupport (a+b) ⊆ star S depth i h X0 Q0 := by
  intro p hp
  rcases Finset.mem_union.mp (he hp) with hx | hq
  · exact Finset.mem_union_left _ hx
  · obtain ⟨q,hq,hpq⟩ := Finset.mem_biUnion.mp hq
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨q,Finset.mem_union_left _ hq,hpq⟩)
end QEC.Coding.BDL26RXFiniteBlockTransport
