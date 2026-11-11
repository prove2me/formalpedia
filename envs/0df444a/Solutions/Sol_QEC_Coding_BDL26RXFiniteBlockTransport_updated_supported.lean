-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.updated_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:24:20.940804+00:00
-- url     : https://prove2.me/submissions/1e1909e6-2805-40f1-b9bb-1d33ad33347e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_input_supported_star
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_correction_difference_supported
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
    hammingSupport (updated S depth i h a b) ⊆ star S depth i h X0 Q0 := by
  have he' := input_supported_star S depth i h X0 Q0 a b he
  have hc := correction_difference_supported S depth i h X0 Q0 a b he
  apply support_of_zero_off
  intro p hp
  have h1 := zero_off_support _ _ he' p hp
  have h2 := zero_off_support _ _ hc p hp
  change (a p+b p)+(run S depth i h a).correction p+(run S depth i h b).correction p=0
  change a p+b p=0 at h1
  change (run S depth i h a).correction p+(run S depth i h b).correction p=0 at h2
  rw [h1,zero_add]
  exact h2
end QEC.Coding.BDL26RXFiniteBlockTransport
