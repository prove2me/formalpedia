-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.x_error_nonincident_q_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:47:19.277693+00:00
-- url     : https://prove2.me/submissions/e9b9703a-99da-4e8b-ab75-f11fa47865f8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_zero_off_support
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_x_flow_nonincident_q
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_region_restrict_extend_disjoint

section
noncomputable section
namespace QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
private theorem extend_restrict_of_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : Finset ι) (w : Word BDL26Field ι) (hw : hammingSupport w ⊆ Y) :
    extendWordLinear Y (restrictWordLinear Y w)=w := by
  funext p
  change extendLocalSignal Y (restrictWordLinear Y w) p=w p
  by_cases hp : p ∈ Y
  · rw [extendLocalSignal,dif_pos hp]
    rfl
  · rw [extendLocalSignal,dif_neg hp,zero_off_support w Y hw p hp]
end QEC.Coding.BDL26RXXStarTransport
end
end

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
theorem _root_.solution (x : XCoord S i) (q : QCoord S i)
    (hq : q ∉ incidentQ S depth i x) (e : Upper S depth i)
    (he : hammingSupport e ⊆ (rxLx S depth i h).correctionRegion x) :
    restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
      ((indexedFamily S depth).coboundary1 i.succ e)=0 := by
  change restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
    ((indexedDecoderData S depth).family.coboundary1 i.succ e)=0
  have hext := extend_restrict_of_support ((rxLx S depth i h).correctionRegion x) e he
  rw [← hext, (rxContract S depth i h).support_decomposition.cxDelta1_decomposition, map_add,
    x_flow_nonincident_q S depth i h x q hq, add_zero]
  apply region_restrict_extend_disjoint
  apply Finset.disjoint_left.mpr
  intro p hpx hpq
  have hcx := ((rxData S depth i h).topCenter_x_iff x p).mp hpx
  have hcq := ((rxData S depth i h).topCenter_q_iff q p).mp hpq
  rw [hcx] at hcq
  cases hcq
end QEC.Coding.BDL26RXXStarTransport
