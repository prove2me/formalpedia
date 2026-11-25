-- Prove2me | solution 1 for PI.QnCovHat2W.sum_sgnL_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:43.814503+00:00
-- url     : https://prove2.me/submissions/8f4f2619-93df-45ee-984c-3e99b90471e6

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
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
theorem _root_.solution {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin (r + 1) → α) (H : (Fin (r + 1) → α) → M) :
    ∑ x, sgnL x e • H x = ∑ j : Fin (r + 1), ((-1 : ℂ) ^ (j : ℕ)) •
      ∑ y : Fin r → α, sgnL y (e ∘ j.succAbove) • H (Fin.cons (e j) y) := by
  have hexp : ∀ (x0 : α) (y : Fin r → α), sgnL (Fin.cons x0 y : Fin (r + 1) → α) e =
      ∑ j : Fin (r + 1), (-1 : ℂ) ^ (j : ℕ) *
        ((if x0 = e j then 1 else 0) * sgnL y (e ∘ j.succAbove)) := by
    intro x0 y
    unfold sgnL
    rw [Matrix.det_succ_row_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
    congr 2
    all_goals first
      | (simp [Matrix.of_apply]; done)
      | (congr 1; ext k j'; simp [Matrix.submatrix_apply, Matrix.of_apply])
  have step : ∀ (x0 : α) (y : Fin r → α),
      sgnL (Fin.cons x0 y : Fin (r + 1) → α) e • H (Fin.cons x0 y) =
        ∑ j : Fin (r + 1), if x0 = e j then
          ((-1 : ℂ) ^ (j : ℕ) • (sgnL y (e ∘ j.succAbove) • H (Fin.cons (e j) y))) else 0 := by
    intro x0 y
    rw [hexp, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · subst h
      rw [one_mul, mul_smul]
    · rw [zero_mul, mul_zero, zero_smul]
  rw [sum_fun_succ]
  simp_rw [step]
  conv_lhs => arg 2; ext x0; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp
end PI.QnCovHat2W
