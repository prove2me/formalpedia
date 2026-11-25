-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_le_belowNat_of_add_two_le_aedb9d1a4179
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:37:42.092442+00:00
-- url     : https://prove2.me/submissions/4ad0f0ea-a340-4b8a-bbe6-c7193caa3bde

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalDoublePointsGeneric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
namespace GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
theorem _root_.solution {x : WithBot ℕ∞} {d : ℕ}
    (h : x + 1 + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) : x ≤ belowNat d := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add, ← WithBot.coe_add, top_add] at h
        exact_mod_cast h
      exact absurd (WithBot.coe_le_coe.1 h2) (by simp)
    | coe k =>
      have h2 : k + 1 + 1 ≤ d + 1 := by exact_mod_cast h
      cases d with
      | zero => omega
      | succ e => show ((k : ℕ∞) : WithBot ℕ∞) ≤ ((e : ℕ) : WithBot ℕ∞); exact_mod_cast (by omega : k ≤ e)
end GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
