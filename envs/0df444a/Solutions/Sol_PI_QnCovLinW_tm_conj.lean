-- Prove2me | solution 1 for PI.QnCovLinW.tm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:07:56.677618+00:00
-- url     : https://prove2.me/submissions/b9e4e477-3d07-4270-9d66-44f4109308c9

import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantLinearProduct_OfFnProdSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovLinW
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovLinW
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (h : Q * P = 1) (u : ℂ) (a b : Fin n) :
    Tm (Econj E P Q) u a b = ∑ x : Fin n × Fin n, (P x.1 a * Q b x.2) • Tm E u x.1 x.2 := by
  have hQP : ∑ c, P c a * Q b c = if a = b then 1 else 0 := by
    have h1 := congrFun (congrFun h b) a
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    rw [show (∑ c, P c a * Q b c) = ∑ c, Q b c * P c a from Finset.sum_congr rfl fun c _ => mul_comm _ _, h1]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  simp only [Tm, Econj, smul_add, Finset.sum_add_distrib, Fintype.sum_prod_type, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_smul, hQP]
  split_ifs <;> simp
end PI.QnCovLinW
