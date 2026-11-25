-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.Amat_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:39:40.845748+00:00
-- url     : https://prove2.me/submissions/8dca2d3d-a5c5-4df3-a8ad-5cd35ef54a70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Alin_apply
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_A_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) : Amat ε e f s * Amat ε e f s⁻¹ = 1 := by
  unfold Amat
  rw [← LinearMap.toMatrix'_comp]
  have hid : Alin ε e f s ∘ₗ Alin ε e f s⁻¹ = LinearMap.id := LinearMap.ext fun v => by
    rw [LinearMap.comp_apply, Alin_apply, Alin_apply, A_inv hG s hs, LinearMap.id_apply]
  rw [hid, LinearMap.toMatrix'_id]
end PI.NMeasInv.UnitaryGroupMassFormula
