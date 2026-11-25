-- Prove2me | solution 1 for PI.WGB.detPow_unitri_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:02.351409+00:00
-- url     : https://prove2.me/submissions/23aebd63-e50a-4a6d-ae2c-1c4f2ab2bdc3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Theorems.Thm_PI_WGB_embGL_unitri_B
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (u : GL (Fin n) ℂ) (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) (c : ℤ) : detPow ℂ N (embGL ℂ n N h u) c = 1 := by
  obtain ⟨h1, _, h3⟩ := embGL_unitri_B h u hl hd
  have hdet : (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => h3 j i hij)]
    simp [h1]
  have hu : Matrix.GeneralLinearGroup.det (embGL ℂ n N h u) = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hdet]
    rfl
  unfold detPow
  rw [hu, one_zpow, Units.val_one]
end PI.WGB
