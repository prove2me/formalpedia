-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.input_syndrome_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:27:27.938272+00:00
-- url     : https://prove2.me/submissions/0bf52fc2-a01b-4e16-801b-51e064e79410

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_localized_blocks
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_localized_blocks
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_input_syndrome_support
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_localized_blocks


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
namespace QEC.Coding.BDL26RZPhysicalXStarTransport
theorem _root_.solution (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport ((errorSyndrome S depth i a).val+(errorSyndrome S depth i b).val) ⊆
      syndromeBlocks S depth i odd (Zplus S depth i odd u) :=
  input_syndrome_support S depth i odd _ _ a b (localized_blocks S depth i odd u a b he)
end QEC.Coding.BDL26RZPhysicalXStarTransport
