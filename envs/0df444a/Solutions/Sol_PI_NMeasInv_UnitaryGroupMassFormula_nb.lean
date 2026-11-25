-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.nb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:07.300995+00:00
-- url     : https://prove2.me/submissions/d8508a1e-0b3c-4f0b-9946-fef02b53c309

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_ConjSubMulVec
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
variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG
omit hG
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution {κ lam : ℝ} {x : ℂ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ lam⁻¹ ∨ x = 0) : ‖(κ : ℂ) * x‖ ≤ lam⁻¹ * ‖x‖ := by
  rcases hκ with h | h
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  · simp [h]
end PI.NMeasInv.UnitaryGroupMassFormula
