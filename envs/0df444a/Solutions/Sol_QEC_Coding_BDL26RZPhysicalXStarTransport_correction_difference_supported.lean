-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.correction_difference_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:26:37.822996+00:00
-- url     : https://prove2.me/submissions/f6cc3e62-cf99-4e1e-8fca-73b52a1f714f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_localized_blocks
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_localized_blocks
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_correction_difference_support
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
    hammingSupport ((run S depth i odd a).correction+(run S depth i odd b).correction) ⊆
      zBlocks S depth i odd (Zplus S depth i odd u) :=
  correction_difference_support S depth i odd _ _ a b (localized_blocks S depth i odd u a b he)
end QEC.Coding.BDL26RZPhysicalXStarTransport
