-- Prove2me | solution 1 for PI.QnCovHat2W.sum_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:47.602141+00:00
-- url     : https://prove2.me/submissions/29f3df82-c803-4183-88e2-f75c65c6d487

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_GGEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SumSgnLProdCol
import Theorems.Thm_PI_QnCovHat2W_sum_fun_succ


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
theorem _root_.solution {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (p : Fin (m + 2) → α → ℂ) (f g : α → ℂ) (Φ : (Fin m → α) → M) :
    ∑ x : Fin (m + 2) → α, (f (x 0) * g (x 1) * ∏ k, p k (x k)) • Φ (fun k => x k.succ.succ) =
      ((∑ z, f z * p 0 z) * (∑ z, g z * p 1 z)) •
        ∑ y : Fin m → α, (∏ k, p k.succ.succ (y k)) • Φ y := by
  rw [sum_fun_succ]
  simp_rw [sum_fun_succ (r := m)]
  simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Fin.prod_univ_succ, Fin.succ_zero_eq_one]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_smul, Finset.smul_sum, smul_smul]
  symm
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun x1 _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 _ =>
    Finset.sum_congr rfl fun y _ => ?_
  congr 1
  ring
end PI.QnCovHat2W
