-- Prove2me | solution 1 for PI.RL.W.RE_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:12:18.659607+00:00
-- url     : https://prove2.me/submissions/37408952-3d6d-467b-b73b-007f727f5bac

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
section
open MvPolynomial
noncomputable section
namespace PI.RL.W
open PI.RL
section
variable {K : Type} [Field K] {k : ℕ}
private theorem pderiv_mul_eq {σ : Type*} {R : Type*} [CommRing R] (i : σ) (f g : MvPolynomial σ R) :
    pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
end
end PI.RL.W
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.RL PI.RL.W
open PI.RL
variable {K : Type} [Field K] {k : ℕ}
namespace PI.RL.W
theorem _root_.solution (a b : Fin k) (f g : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b (f * g) = RE K k a b f * g + f * RE K k a b g := by
  simp only [PI.RL.RE, pderiv_mul_eq, mul_add, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum]
  congr 1 <;> (refine Finset.sum_congr rfl (fun t _ => ?_); ring)
end PI.RL.W
