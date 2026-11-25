-- Prove2me | solution 1 for PI.WGB.torus_fix_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:52.313803+00:00
-- url     : https://prove2.me/submissions/09c6cb22-7492-4ba7-835c-50a5bc4c35cc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RenameTauHomogB
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGB_embGL_diag_B
import Theorems.Thm_PI_WGB_rowAct_diag_homog
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
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (g : MvPolynomial (Fin N × Fin N) ℂ)
    (m : Fin n → ℕ) (hm : IsWeightedHomogeneous (wnB n N) g m) (t : Fin n → ℂˣ) :
    sqAct ℂ N lam (embGL ℂ n N h (diagGL ℂ n t)) g =
      ((∏ j, t j ^ ((m j : ℤ) + lam.detShift) : ℂˣ) : ℂ) • g := by
  unfold sqAct
  rw [embGL_diag_B, Matrix.diagonal_transpose, rowAct_diag_homog _ _ _ hm, smul_smul]
  congr 1
  have hdet : Matrix.GeneralLinearGroup.det (embGL ℂ n N h (diagGL ℂ n t)) = ∏ j, t j := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, embGL_diag_B, Matrix.det_diagonal, Units.coe_prod]
    subst h
    rw [Fin.prod_univ_castSucc]
    simp [dB]
  unfold detPow
  rw [hdet]
  have hchi : chiB (fun j => ((t j : ℂˣ) : ℂ)) m = ((∏ j, t j ^ (m j) : ℂˣ) : ℂ) := by
    simp [chiB, Units.coe_prod]
  rw [hchi, ← Units.val_mul]
  congr 1
  simp only [zpow_add, Finset.prod_mul_distrib, zpow_natCast, Finset.prod_zpow]
  rw [mul_comm]
end PI.WGB
