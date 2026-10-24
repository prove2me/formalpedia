-- Prove2me | solution 1 for PandoraBO.Private20261023.capped_reward_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:23:24.48591+00:00
-- url     : https://prove2.me/submissions/8f4ee2c4-842e-42f0-9eba-667a932101bd

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_pathwise_capped_reward_upper_bound
import Theorems.Thm_PandoraBO_Private20261023_policy_capped_integrability_and_excess
import Theorems.Thm_PandoraBO_Private20261023_policy_terminal_measurable_integrable
import Mathlib.Tactic.Linarith

/-! Integrate the pathwise cap upper bound and cancel the expected excess
against the reservation-index opening cost. This reduction depends on the
explicitly tracked nonanticipation and integrability foundation. -/

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory PandoraBO

theorem solution {n : ℕ} (M : Instance n)
    (multiplier : ℝ) (hpos : 0 < multiplier) (z : Box n → ℝ)
    (hz : reservationIndices M multiplier z) (π : Policy n) :
    value M multiplier π ≤
      ∫ ω : Outcome n, fullInformationPayoff (fun i => min (ω.1 i) (z i)) ∂jointLaw M := by
  obtain ⟨hcap, hsurplus, hcancel⟩ :=
    PandoraBO.Private20261023.policy_capped_integrability_and_excess M multiplier z hz π
  have hreward :=
    (PandoraBO.Private20261023.policy_terminal_measurable_integrable M π).2.2.1
  have hbound : expectedReward M π ≤
      (∫ ω : Outcome n, fullInformationPayoff (fun i => min (ω.1 i) (z i)) ∂jointLaw M) +
        multiplier * expectedCost M π := by
    unfold expectedReward
    calc
      (∫ ω, terminalReward π ω ∂jointLaw M) ≤
          ∫ ω : Outcome n,
            fullInformationPayoff (fun i => min (ω.1 i) (z i)) +
              (∑ k : Fin (n + 1), if occupied (terminalHistory π ω) k then
                max (observedReward (terminalHistory π ω) k -
                  z (observedBox (terminalHistory π ω) k)) 0 else 0) ∂jointLaw M :=
        integral_mono hreward (hcap.add hsurplus)
          (fun ω => PandoraBO.Private20261023.pathwise_capped_reward_upper_bound π ω z)
      _ = _ := by rw [integral_add hcap hsurplus, hcancel]
  unfold value
  linarith
