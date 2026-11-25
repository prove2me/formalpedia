-- Prove2me | solution 1 for PI.WGL.io_fixed_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:29:28.997887+00:00
-- url     : https://prove2.me/submissions/5e34d1c4-26cc-4942-9204-590513b202a0

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
theorem _root_.solution {n : ℕ} (lam : DomWeight (n + 1)) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hU : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) f = f)
    (a b : Fin n) (hab : a < b) : pol ℂ a.castSucc b.castSucc f = 0 := by
  have hne : a ≠ b := ne_of_lt hab
  have key : ∀ m : ℕ, (rowGen ℂ a.castSucc b.castSucc f - Polynomial.C f).eval (C (m : ℂ)) ∈
      (⊥ : Submodule ℂ (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) := by
    intro m
    rw [Submodule.mem_bot, Polynomial.eval_sub, Polynomial.eval_C, PI.WHw.eval_rowGen, sub_eq_zero]
    have hdet : (1 + Matrix.single a b (m : ℂ)).det ≠ 0 := by
      rw [det_one_add_single, if_neg hne]; exact one_ne_zero
    let g := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
    have hgv : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b (m : ℂ) := rfl
    have hup : ∀ i j, j < i → g i j = 0 := by
      intro i j hji
      have hij : i ≠ j := ne_of_gt hji
      show (1 + Matrix.single a b (m : ℂ)) i j = 0
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_neg hij, zero_add]
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact absurd (lt_trans hab hji) (lt_irrefl _)
    have hdiag : ∀ i, g i i = 1 := by
      intro i
      show (1 + Matrix.single a b (m : ℂ)) i i = 1
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_true]
      rw [if_neg]; · simp
      rintro ⟨rfl, h⟩; exact hne h.symm
    have h1 := hU g hup hdiag
    have hT := embGL_transvec g a b (m : ℂ) hgv
    have hdet1 : detPow ℂ (n + 1) (embGL ℂ n (n + 1) rfl g) lam.detShift = 1 := by
      unfold detPow
      have hd : Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hT, det_one_add_single,
          if_neg (fun h => hne (Fin.castSucc_injective _ h).symm)]
        rfl)
      rw [hd, one_zpow, Units.val_one]
    unfold sqAct at h1
    rw [hdet1, one_smul, hT] at h1
    exact h1
  have := PI.WHw.coeff_mem_of_eval ⊥ _ key 1
  rw [Submodule.mem_bot, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by omega), sub_zero] at this
  rw [pol_eq_rowDiv]
  exact this
end PI.WGL
