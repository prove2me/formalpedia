-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.lower_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:32:15.0992+00:00
-- url     : https://prove2.me/submissions/9a0edf67-3a02-484c-b087-58e2d6cfad27

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_Q0_card_le_seven
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_lower_supported


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
theorem _root_.solution (above : 3 ≤ i.val) (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    HammingWeight (lowerError S depth i odd a b) ≤ (Q0 S depth i odd u).card ∧ (Q0 S depth i odd u).card ≤ 7 := by
  rw [HammingWeight_eq_card_hammingSupport]
  exact ⟨Finset.card_le_card (lower_supported S depth i odd above u a b he),Q0_card_le_seven S depth i odd u⟩
end QEC.Coding.BDL26RZPhysicalXStarTransport
