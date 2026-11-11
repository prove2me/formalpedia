-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.coarse_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:23:03.99262+00:00
-- url     : https://prove2.me/submissions/d71fc24e-224e-4362-9e20-2b979214f582

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_coarse_apply
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_support_of_zero_off


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
    hammingSupport (coarseSum S depth i h a b).val ⊆ incidentZ S depth i x := by
  apply support_of_zero_off
  intro z hz
  rw [coarse_apply S depth i h x a b he z]
  apply Finset.sum_eq_zero
  intro q hq
  have hqz : (state S i.val).presentation.qz q z ≠ true := by
    intro hh
    exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨q,hq,hh⟩⟩)
  rw [if_neg hqz,mul_zero]
end QEC.Coding.BDL26RXXStarTransport
