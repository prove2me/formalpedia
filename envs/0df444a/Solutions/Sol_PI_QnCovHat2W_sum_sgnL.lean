-- Prove2me | solution 1 for PI.QnCovHat2W.sum_sgnL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:21:19.151534+00:00
-- url     : https://prove2.me/submissions/ad2efc45-31c2-46a8-a47a-2bbaf94eba20

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
import Theorems.Thm_PI_QnCovHat2W_sgnL_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovHat2W
theorem _root_.solution {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin r → α) (g : (Fin r → α) → M) :
    ∑ x, sgnL x e • g x = ∑ π : Equiv.Perm (Fin r), ((Equiv.Perm.sign π : ℤ) : ℂ) • g (e ∘ π) := by
  simp_rw [sgnL_eq_sum, Finset.sum_smul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun σ => by simp [Equiv.Perm.sign_inv, Equiv.Perm.inv_def])
end PI.QnCovHat2W
