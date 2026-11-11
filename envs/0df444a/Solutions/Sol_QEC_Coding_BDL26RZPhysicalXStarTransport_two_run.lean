-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.two_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:40:35.922975+00:00
-- url     : https://prove2.me/submissions/60906e6a-4979-4218-bd77-935984316e7f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_localized_blocks
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_lower_physical_supported
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_lower_weight
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_two_run
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_localized_blocks
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_lower_weight
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_two_run
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_potential_oldX_zero
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_localized_blocks
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_lower_weight
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_two_run


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
    ∃ p : Potential S depth i,
      Pullback S depth i odd (Q0 S depth i odd u) (Z0 S depth i odd u) a b p ∧
      hammingSupport (lowerError S depth i odd a b) ⊆
        BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) (downX S depth i odd u) ∧
      HammingWeight (lowerError S depth i odd a b) ≤ (Q0 S depth i odd u).card ∧
      (Q0 S depth i odd u).card ≤ 7 ∧
      (∀ x : (Old S depth i).X, ∀ c : BDL26FiniteTannerSquare.Two, read0 S depth i odd p (.inr (x,c))=0) := by
  obtain ⟨p,hp⟩ := BDL26RZFiniteBlockTransport.two_run S depth i odd (by omega) _ _ a b
    (localized_blocks S depth i odd u a b he)
  exact ⟨p,hp,lower_physical_supported S depth i odd above u a b he,
    (lower_weight S depth i odd above u a b he).1,(lower_weight S depth i odd above u a b he).2,
    potential_oldX_zero S depth i odd _ _ p hp.2.2.2.2.2.2.2.2.1⟩
end QEC.Coding.BDL26RZPhysicalXStarTransport
