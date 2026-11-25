-- Prove2me | solution 1 for PI.WGL.capF_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:58.185796+00:00
-- url     : https://prove2.me/submissions/9bf61e02-e062-4670-ad54-1c65bc77cb3b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
import Definitions.Def_Lemmata_GeneralBFactRight_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliZ
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
namespace PI.WGL
theorem _root_.solution (hC : CapScalar) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) (i : Fin n) (v : ℤ) :
    capF h lam i v (φ s) = (∏ j : Fin n, ((((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ) : ℤ)) : ℂ)) • φ s := by
  rw [capF, LinearMap.smul_apply, hC h lam mu φ hφ s hs, smul_smul]
  congr 1
  have : ((-1 : ℂ) ^ n) = ∏ _j : Fin n, (-1 : ℂ) := by simp
  rw [this, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast; ring
end PI.WGL
