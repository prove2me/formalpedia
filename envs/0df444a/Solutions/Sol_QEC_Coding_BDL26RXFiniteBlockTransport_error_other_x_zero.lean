-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.error_other_x_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:15:51.109961+00:00
-- url     : https://prove2.me/submissions/4ca0057c-c810-4f5b-b9cb-f2fdbc84e8b4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_x_q_disjoint
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_zero_off_support
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    (y : XCoord S i) (hy : y ∉ X0) (a b : Upper S depth i)
    (he : Localized S depth i h X0 Q0 a b) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) (a+b)=0 := by
  funext p
  apply zero_off_support _ _ he p.val
  intro hp
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨x,hx,hpx⟩ := Finset.mem_biUnion.mp hp
    have hyx : y≠x := fun hh => hy (hh.symm ▸ hx)
    exact (Finset.disjoint_left.mp
      ((rxData S depth i h).cx_correction_regions_pairwise_disjoint y x hyx)) p.property hpx
  · obtain ⟨q,_,hpq⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.disjoint_left.mp (x_q_disjoint S depth i h y q)) p.property hpq
end QEC.Coding.BDL26RXFiniteBlockTransport
