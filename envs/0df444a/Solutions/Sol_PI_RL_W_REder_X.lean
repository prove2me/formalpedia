-- Prove2me | solution 1 for PI.RL.W.REder_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:12:22.824556+00:00
-- url     : https://prove2.me/submissions/519f270a-e3c5-44bf-87a2-bf401ed9436a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowLetter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_DetDer
import Theorems.Thm_PI_RL_W_derivation_sum_apply

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
namespace PI.RL.W
theorem _root_.solution (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (i j : Fin k) :
    REder K k a b (X (i, j)) = if i = b then X (a, j) else 0 := by
  unfold REder
  rw [derivation_sum_apply]
  simp only [Derivation.smul_apply, pderiv_X, smul_eq_mul]
  by_cases h : i = b
  · subst h
    simp [Pi.single_apply, mul_ite]
  · simp [Pi.single_apply, h]
end PI.RL.W
