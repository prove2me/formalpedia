-- Prove2me | solution 1 for PI.RL.W.rowLetter_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:51.139328+00:00
-- url     : https://prove2.me/submissions/1bdacf93-f5b8-4e8f-90f2-1f028f38bfae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowLetter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_Development
import Theorems.Thm_PI_RL_W_theta_X
import Theorems.Thm_PI_RL_W_euler_theta

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
theorem _root_.solution (hC : ChainRule) (hV : VecX) (hK : KeyCov) (hH : HdHom) : PI.RowLetter := by
  intro K _ m vec d a b P hP
  rw [hC K m vec a b P]
  cases vec
  · have hE := euler_theta hH K m false d P hP
    by_cases hab : a = b
    · subst hab
      have hL : ∑ c, theta K m false (pderiv c P) * RE K (m + 1) a a (Nv K m false c) =
          ∑ c, theta K m false (pderiv c P) * Nv K m false c -
            theta K m false (pderiv a P) * Nv K m false a := by
        have hc : ∀ c, RE K (m + 1) a a (Nv K m false c) =
            Nv K m false c - (if a = c then Nv K m false a else 0) := by
          intro c
          rw [hK K m a a c]
          simp
        simp only [hc, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
      rw [hL, hE]
      simp only [TE, Bool.false_eq_true, if_true, if_false, map_sub, map_smul, map_mul, theta_X]
      rw [mul_comm (Nv K m false a)]
    · have hc : ∀ c, RE K (m + 1) a b (Nv K m false c) =
          -(if a = c then Nv K m false b else 0) := by
        intro c
        rw [hK K m a b c]
        simp [hab]
      simp only [hc, mul_neg, mul_ite, mul_zero, Finset.sum_neg_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      simp [TE, hab, theta_X] <;> ring
  · have hc : ∀ c, RE K (m + 1) a b (Nv K m true c) = if c = b then Nv K m true a else 0 :=
      fun c => hV K m a b c
    simp only [hc, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [TE, if_true, map_mul, theta_X]
    rw [mul_comm]
end PI.RL.W
