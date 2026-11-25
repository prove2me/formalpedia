-- Prove2me | solution 1 for PI.ScRefExists.GWG.hG_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:44.039014+00:00
-- url     : https://prove2.me/submissions/a965f049-1a6f-4020-b2c6-4cdf95c858cf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue
import Theorems.Thm_PI_ScRefExists_GWG_hG_add_left
import Theorems.Thm_PI_ScRefExists_GWG_hG_add_right
import Theorems.Thm_PI_ScRefExists_GWG_hG_zsmul_left
import Theorems.Thm_PI_ScRefExists_GWG_hG_zsmul_right
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GWG
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.GWG
theorem _root_.solution (q₁ q₂ : ℤ) (x₁ x₂ y₁ y₂ : Fin I.n → I.E) :
    hG I (q₁ • x₁ + q₂ • x₂) (q₁ • y₁ + q₂ • y₂) =
      (q₁ : I.E) ^ 2 * hG I x₁ y₁ + (q₁ : I.E) * (q₂ : I.E) * (hG I x₁ y₂ + hG I x₂ y₁) +
        (q₂ : I.E) ^ 2 * hG I x₂ y₂ := by
  simp only [hG_add_left, hG_add_right, hG_zsmul_left, hG_zsmul_right]
  ring
end PI.ScRefExists.GWG
