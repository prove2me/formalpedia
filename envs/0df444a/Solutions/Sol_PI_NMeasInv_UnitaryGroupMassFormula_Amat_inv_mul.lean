-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.Amat_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:24:41.603807+00:00
-- url     : https://prove2.me/submissions/549f47af-b2bb-4b05-ab46-c8f9446a52ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Alin_apply
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_A_inv
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
open Matrix
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) : Amat ε e f s⁻¹ * Amat ε e f s = 1 := by
  unfold Amat
  rw [← LinearMap.toMatrix'_comp]
  have hid : Alin ε e f s⁻¹ ∘ₗ Alin ε e f s = LinearMap.id := LinearMap.ext fun v => by
    rw [LinearMap.comp_apply, Alin_apply, Alin_apply, LinearMap.id_apply]
    have h1 := A_inv hG s⁻¹ (fun b => by simp [hs b]) v
    rwa [inv_inv] at h1
  rw [hid, LinearMap.toMatrix'_id]
end PI.NMeasInv.UnitaryGroupMassFormula
