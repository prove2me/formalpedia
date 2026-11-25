-- Prove2me | solution 1 for PI.RL.W.hdHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:12:39.701393+00:00
-- url     : https://prove2.me/submissions/6e80df13-e432-4d00-a719-9cafa5f0afd4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowLetter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_ChainRule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.RL PI.RL.W
open PI.RL
namespace PI.RL.W
theorem _root_.solution : HdHom := by
  intro K _ k d P hP
  unfold PI.RL.Hd at hP
  rw [mem_restrictSupport_iff] at hP
  intro μ hμ
  have h2 := hP (mem_support_iff.mpr hμ)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simpa using h2
end PI.RL.W
