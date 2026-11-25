-- Prove2me | solution 1 for PI.WGL.EqvWt.coeff_eq_of_eqv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:32.90066+00:00
-- url     : https://prove2.me/submissions/72948ef3-d81a-430a-a59f-6b64a3766971

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
import Theorems.Thm_PI_WGL_EqvWt_coeff_sqAct_diag
import Theorems.Thm_PI_WGL_EqvWt_embGL_diagGL
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
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open PI.WGL.EqvWt
namespace PI.WGL.EqvWt
theorem _root_.solution {n : ℕ} (lam : DomWeight (n + 1)) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hφ : IsEqv rfl mu lam φ) (t : Fin n → ℂˣ) (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu)
    (κ : ℂ) (hκ : sqAct ℂ n mu (diagGL ℂ n t) s = κ • s) (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ)
    (hm : coeff m (φ s) ≠ 0) :
    (∏ i, (t i : ℂ)) ^ lam.detShift * ∏ i, (t i : ℂ) ^ rowDeg m (Fin.castSucc i) = κ := by
  have h1 := hφ.2 (diagGL ℂ n t) s hs
  rw [hκ, map_smul, embGL_diagGL] at h1
  have h2 := congrArg (coeff m) h1
  rw [coeff_smul, coeff_sqAct_diag, smul_eq_mul, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc] at h2
  simp only [Fin.coe_castSucc, Fin.is_lt, dite_true, dif_pos, Fin.eta, Fin.val_last, lt_self_iff_false,
    dite_false, Units.val_one, one_pow, mul_one] at h2
  exact mul_right_cancel₀ hm (by linear_combination (-1 : ℂ) * h2)
end PI.WGL.EqvWt
