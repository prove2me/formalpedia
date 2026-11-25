-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_le_of_add_one_le_natCast_add_one_6b5626c06405
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:32:47.909425+00:00
-- url     : https://prove2.me/submissions/c942b800-d6c0-45a2-bd32-bac36fa54d0c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
theorem _root_.solution {x : WithBot ℕ∞} {n : ℕ}
    (h : x + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) : x ≤ (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        exact_mod_cast h
      rw [top_add, WithBot.coe_le_coe] at h'
      exact absurd h' (by simp)
    | coe m =>
      have h' : (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        simpa using h
      have h'' : m + 1 ≤ n + 1 := by exact_mod_cast WithBot.coe_le_coe.mp h'
      have : m ≤ n := by omega
      exact_mod_cast this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
