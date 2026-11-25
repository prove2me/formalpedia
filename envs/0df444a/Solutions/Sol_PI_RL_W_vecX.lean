-- Prove2me | solution 1 for PI.RL.W.vecX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:12:43.476883+00:00
-- url     : https://prove2.me/submissions/427fbacb-e9c2-4275-8127-5d63e77f00ba

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
theorem _root_.solution : VecX := by
  intro K _ m a b c
  have hp : ∀ t : Fin (m + 1),
      pderiv (b, t) (X (c, 0) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) =
        if c = b ∧ t = 0 then 1 else 0 := by
    intro t
    rw [pderiv_X]
    by_cases h : c = b ∧ t = 0
    · obtain ⟨rfl, rfl⟩ := h; simp
    · rw [if_neg h, Pi.single_apply, if_neg]
      intro he
      simp only [Prod.mk.injEq] at he
      exact h ⟨he.1, he.2.symm⟩
  simp only [PI.RL.Nv, if_true, PI.RL.RE, hp, mul_ite, mul_one, mul_zero]
  by_cases h : c = b
  · subst h; simp [Finset.sum_ite_eq']
  · simp [h]
end PI.RL.W
