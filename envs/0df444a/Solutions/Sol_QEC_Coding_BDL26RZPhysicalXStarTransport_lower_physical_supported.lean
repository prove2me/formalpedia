-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.lower_physical_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:32:29.651424+00:00
-- url     : https://prove2.me/submissions/f2e4a948-9246-47db-98b7-79401db4a475

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_Q0_subset_lowerStar
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_lower_supported
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    (he : Localized S depth i u a b) : hammingSupport (lowerError S depth i odd a b) ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) (downX S depth i odd u) :=
  (lower_supported S depth i odd above u a b he).trans (Q0_subset_lowerStar S depth i odd u)
end QEC.Coding.BDL26RZPhysicalXStarTransport
