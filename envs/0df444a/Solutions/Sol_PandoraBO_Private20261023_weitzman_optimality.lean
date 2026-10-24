-- Prove2me | solution 1 for PandoraBO.Private20261023.weitzman_optimality
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:05:50.695541+00:00
-- url     : https://prove2.me/submissions/68bb14f3-0561-43ee-af56-64842828a92f

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_gittins_policy_exists
import Theorems.Thm_PandoraBO_Private20261023_capped_reward_upper_bound
import Theorems.Thm_PandoraBO_Private20261023_gittins_capped_reward_identity

/-!
Tracked reduction of Weitzman's theorem to the capped-reward upper bound and
the equality case for Gittins policies. Policy existence is already verified.
The two capped-reward children are substantive open proof obligations, not
assumptions added to the canonical mission statement.
-/

set_option autoImplicit false

open MeasureTheory PandoraBO

theorem solution {n : ℕ} (M : Instance n)
    (multiplier : ℝ) (hpos : 0 < multiplier) :
    (∃ π : Policy n, isGittinsPolicy M multiplier π) ∧
    ∀ π : Policy n, isGittinsPolicy M multiplier π → optimal M multiplier π := by
  refine ⟨PandoraBO.Private20261023.gittins_policy_exists M multiplier hpos, ?_⟩
  intro π hπ ρ
  obtain ⟨z, hz, _hfirst, _hnext⟩ := hπ
  calc
    value M multiplier ρ ≤
        ∫ ω : Outcome n, fullInformationPayoff (fun i => min (ω.1 i) (z i)) ∂jointLaw M :=
      PandoraBO.Private20261023.capped_reward_upper_bound M multiplier hpos z hz ρ
    _ = value M multiplier π :=
      (PandoraBO.Private20261023.gittins_capped_reward_identity
        M multiplier hpos z hz π ⟨z, hz, _hfirst, _hnext⟩).symm
