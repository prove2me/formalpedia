-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.two_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:01:35.421483+00:00
-- url     : https://prove2.me/submissions/b03ab037-505f-449a-a114-600d8ac6aee0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_supported
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_map1_with_potential
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_coarse_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_with_potential
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_coarse_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_with_potential


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
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h X0 a b) =
        updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b) ∧
      (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h X0 a b) =
        (coarseSum S depth i h a b).val ∧
      hammingSupport (Phi S depth i h X0 a b) ⊆ degreeZeroBlocks S depth i h X0 ∧
      hammingSupport (L S depth i h X0 a b) ⊆ neighbors S depth i X0 Q0 ∧
      hammingSupport (coarseSum S depth i h a b).val ⊆ neighborZ S depth i X0 Q0 :=
  ⟨map1_with_potential S depth i h X0 Q0 a b he,lower_syndrome S depth i h X0 Q0 a b he,
    phi_supported S depth i h X0 a b,lower_supported S depth i h X0 Q0 a b he,
    coarse_supported S depth i h X0 Q0 a b he⟩
end QEC.Coding.BDL26RXFiniteBlockTransport
