-- Prove2me | solution 1 for PI.RL.W.euler_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:12:33.658801+00:00
-- url     : https://prove2.me/submissions/2298c90c-ac0d-4d41-af3f-19d6e4e2e499

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowLetter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_Development
import Theorems.Thm_PI_RL_W_theta_X

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
theorem _root_.solution (hH : HdHom) (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ)
    (P : MvPolynomial (Fin (m + 1)) K) (hP : P ∈ Hd K (m + 1) d) :
    ∑ c, theta K m vec (pderiv c P) * Nv K m vec c = (d : K) • theta K m vec P := by
  have h1 := (hH K (m + 1) d P hP).sum_X_mul_pderiv
  have h2 := congrArg (theta K m vec) h1
  simp only [map_sum, map_mul, theta_X, map_nsmul] at h2
  rw [← Nat.cast_smul_eq_nsmul K] at h2
  rw [← h2]
  exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
end PI.RL.W
