-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.updated_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:12:41.708037+00:00
-- url     : https://prove2.me/submissions/ba928009-326f-42bf-a40e-fbaf122c7b92

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_support_of_zero_off
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_zero_off_support


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
    hammingSupport (updated S depth i h a b) ⊆ star1 S depth i h x := by
  apply support_of_zero_off
  intro p hp
  have h1 := zero_off_support (a+b) _ he p (fun hm => hp (Finset.mem_union_left _ hm))
  have h2 := zero_off_support _ _ (correction_difference_supported S depth i h x a b he) p hp
  change a p+b p=0 at h1
  change (run S depth i h a).correction p+(run S depth i h b).correction p=0 at h2
  change (a p+b p)+(run S depth i h a).correction p+(run S depth i h b).correction p=0
  rw [h1,zero_add]
  exact h2
end QEC.Coding.BDL26RXXStarTransport
