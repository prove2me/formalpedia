-- Prove2me | solution 1 for PI.QnLevBasicsW.split_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:18:12.377822+00:00
-- url     : https://prove2.me/submissions/45fafa67-dac0-4c0d-be35-75762f7c7815

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Theorems.Thm_PI_QnLevBasicsW_split_symm_inl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PI.QnLevBasicsW
theorem _root_.solution (p : Fin (2 * (i + r') + k + 1)) (h : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) :
    ∃ b, split k i r' p = Sum.inr b := by
  rcases hs : split k i r' p with a | b
  · exfalso
    have hp : p = (split k i r').symm (Sum.inl a) := by rw [← hs, Equiv.symm_apply_apply]
    have hv := congrArg Fin.val hp
    rw [split_symm_inl] at hv
    have := a.isLt
    omega
  · exact ⟨b, rfl⟩
end PI.QnLevBasicsW
