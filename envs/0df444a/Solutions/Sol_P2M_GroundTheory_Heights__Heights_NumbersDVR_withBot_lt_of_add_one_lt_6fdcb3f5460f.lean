-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_of_add_one_lt_6fdcb3f5460f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:54.827983+00:00
-- url     : https://prove2.me/submissions/85a40168-884a-48a1-a813-ad8ac2a632cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {d : WithBot ℕ∞} {N : ℕ}
    (h : d + 1 < ((N + 1 : ℕ) : WithBot ℕ∞)) : d < ((N : ℕ) : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe x =>
    induction x using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := rfl
      rw [this] at h
      exact absurd h (not_lt.mpr (WithBot.coe_le_coe.mpr le_top))
    | coe k =>
      have h' : ((k + 1 : ℕ) : WithBot ℕ∞) < ((N + 1 : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast h
      have h'' : k + 1 < N + 1 := by exact_mod_cast h'
      have : k < N := by omega
      exact_mod_cast this
end GroundTheory.Heights₂.Heights.NumbersDVR
