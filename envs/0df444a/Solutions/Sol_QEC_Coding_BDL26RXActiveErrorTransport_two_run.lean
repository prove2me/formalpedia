-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.two_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:18:29.699196+00:00
-- url     : https://prove2.me/submissions/1270ec31-a59e-4f71-afa1-3f0d9800b24d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_map1_with_potential
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_lower_weight_le_seven_error
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_map1_with_potential
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_with_potential
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_with_potential


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXActiveErrorTransport
theorem _root_.solution (a b : Upper S depth i) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h a b) =
        updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h a b) ∧
      (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h a b)=(coarseSum S depth i h a b).val ∧
      HammingWeight (L S depth i h a b) ≤ 7*HammingWeight (a+b) :=
  ⟨map1_with_potential S depth i h a b,lower_syndrome S depth i h a b,lower_weight_le_seven_error S depth i h a b⟩
end QEC.Coding.BDL26RXActiveErrorTransport
