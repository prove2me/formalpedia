-- Prove2me | solution 1 for PI.WGL.io_torus_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:59.959284+00:00
-- url     : https://prove2.me/submissions/8dd79bdf-da40-4571-9627-6919e3c26e6e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoPolDiagHw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoXiHw
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_det_one_add_single
import Theorems.Thm_PI_WGL_embGL_transvec
import Theorems.Thm_PI_WGL_pol_eq_rowDiv
import Theorems.Thm_PI_WHw_coeff_mem_of_eval
import Theorems.Thm_PI_WHw_eval_rowGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n)
    (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hT : ∀ t : Fin n → ℂˣ, sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl (diagGL ℂ n t)) f =
      ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) • f)
    (a : Fin n) (hd : lam.detShift ≤ sg.w a) :
    pol ℂ a.castSucc a.castSucc f = ((sg.w a - lam.detShift : ℤ) : ℂ) • f := by
  set d : ℕ := (sg.w a - lam.detShift).toNat with hd'
  have hdz : ((d : ℕ) : ℤ) = sg.w a - lam.detShift := Int.toNat_of_nonneg (by omega)
  have key : ∀ m : ℕ, (rowGen ℂ a.castSucc a.castSucc f - Polynomial.C f * (1 + Polynomial.X) ^ d).eval
      (C (m : ℂ)) ∈ (⊥ : Submodule ℂ (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) := by
    intro m
    have hm0 : (m : ℂ) + 1 ≠ 0 := by norm_cast
    let t : Fin n → ℂˣ := fun j => if j = a then Units.mk0 ((m : ℂ) + 1) hm0 else 1
    have h1 := hT t
    have hgv : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a a (m : ℂ) := by
      ext i j
      simp only [diagGL, Matrix.diagonal_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, t]
      by_cases hij : i = j <;> by_cases hia : i = a <;> simp_all [add_comm] <;> intro h <;> exact absurd h.symm hia
    have hTr := embGL_transvec (diagGL ℂ n t) a a (m : ℂ) hgv
    have hdet : detPow ℂ (n + 1) (embGL ℂ n (n + 1) rfl (diagGL ℂ n t)) lam.detShift =
        ((m : ℂ) + 1) ^ lam.detShift := by
      unfold detPow
      rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hTr,
        det_one_add_single, if_pos rfl]
    have hprod : ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) = ((m : ℂ) + 1) ^ sg.w a := by
      rw [Finset.prod_eq_single a (fun j _ hj => by simp [t, hj]) (by simp), Units.val_zpow_eq_zpow_val]
      simp [t]
    unfold sqAct at h1
    rw [hdet, hTr, hprod] at h1
    have hz : ((m : ℂ) + 1) ^ sg.w a = ((m : ℂ) + 1) ^ lam.detShift * ((m : ℂ) + 1) ^ d := by
      rw [← zpow_natCast, hdz, ← zpow_add₀ hm0]
      congr 1
      ring
    rw [hz, ← smul_smul] at h1
    have h2 := smul_right_injective _ (zpow_ne_zero _ hm0) h1
    rw [Submodule.mem_bot, Polynomial.eval_sub, PI.WHw.eval_rowGen, sub_eq_zero, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
    rw [show (1 + C (m : ℂ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ^ d = C (((m : ℂ) + 1) ^ d) by
      rw [map_pow, map_add, map_one, add_comm (C (m : ℂ)) 1], mul_comm, ← smul_eq_C_mul]
    exact h2
  have := PI.WHw.coeff_mem_of_eval ⊥ _ key 1
  rw [Submodule.mem_bot, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
    Nat.choose_one_right, sub_eq_zero] at this
  rw [pol_eq_rowDiv]
  unfold rowDiv
  rw [this, ← hdz, Int.cast_natCast, smul_eq_C_mul, mul_comm, map_natCast]
end PI.WGL
