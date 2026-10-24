-- Prove2me | solution 1 for PandoraBO.Private20261023.gittins_capped_reward_identity
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:23:23.953191+00:00
-- url     : https://prove2.me/submissions/ec446029-84aa-498e-a0cf-68fb4e7a5f61

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_gittins_pathwise_capped_reward_identity
import Theorems.Thm_PandoraBO_Private20261023_policy_capped_integrability_and_excess
import Mathlib.Tactic.Linarith

/-! Integrate the Gittins pathwise cap identity and cancel the expected
excess against the reservation-index opening cost. The pending analytic
foundation is exposed as a tracked dependency rather than an assumption. -/

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory PandoraBO

theorem solution {n : ℕ} (M : Instance n)
    (multiplier : ℝ) (hpos : 0 < multiplier) (z : Box n → ℝ)
    (hz : reservationIndices M multiplier z) (π : Policy n)
    (hπ : isGittinsPolicy M multiplier π) :
    value M multiplier π =
      ∫ ω : Outcome n, fullInformationPayoff (fun i => min (ω.1 i) (z i)) ∂jointLaw M := by
  obtain ⟨hcap, hsurplus, hcancel⟩ :=
    PandoraBO.Private20261023.policy_capped_integrability_and_excess M multiplier z hz π
  have hid : expectedReward M π =
      (∫ ω : Outcome n, fullInformationPayoff (fun i => min (ω.1 i) (z i)) ∂jointLaw M) +
        multiplier * expectedCost M π := by
    unfold expectedReward
    calc
      (∫ ω, terminalReward π ω ∂jointLaw M) =
          ∫ ω : Outcome n,
            fullInformationPayoff (fun i => min (ω.1 i) (z i)) +
              (∑ k : Fin (n + 1), if occupied (terminalHistory π ω) k then
                max (observedReward (terminalHistory π ω) k -
                  z (observedBox (terminalHistory π ω) k)) 0 else 0) ∂jointLaw M := by
        apply integral_congr_ae
        exact ae_of_all _ (fun ω =>
          PandoraBO.Private20261023.gittins_pathwise_capped_reward_identity M multiplier
            hpos z hz π hπ ω)
      _ = _ := by rw [integral_add hcap hsurplus, hcancel]
  unfold value
  linarith
