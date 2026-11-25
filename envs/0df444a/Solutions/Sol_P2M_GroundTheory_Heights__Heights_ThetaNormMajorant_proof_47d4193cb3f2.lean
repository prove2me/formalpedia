-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ThetaNormMajorant_proof_47d4193cb3f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:50:53.181817+00:00
-- url     : https://prove2.me/submissions/c4122a30-0e47-45ea-bfe1-d3cd90116301

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaNormMajorant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaNormMajorant_isSymm_of_posDef_17a751f32486
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_summable_exp_qf_4231a987a485


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Real
namespace GroundTheory.Heights₂.Heights
namespace ThetaNormMajorant
theorem _root_.solution (h : ThetaSummandNorm.Statement) : ThetaNormMajorant.Statement := by
  intro g X Y a b u₁ u₂ hY
  have hS := KThetaNormMajorant.isSymm_of_posDef hY
  set z : Fin g → ℂ := periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ) with hz
  set E : ℝ := exp (-π * qf Y u₁) with hE
  have hEpos : 0 < E := exp_pos _
  have hterm : ∀ k : Fin g → ℤ,
      ‖thetaSummand X Y a b z k‖ = exp (-π * qf Y (intVec k + a + u₁)) * E⁻¹ := by
    intro k
    rw [← h g X Y a b u₁ u₂ k hS, mul_inv_cancel_right₀ hEpos.ne']
  have hG : Summable fun k : Fin g → ℤ => exp (-π * qf Y (intVec k + a + u₁)) := by
    have := KTheta.summable_exp_qf Y hY π Real.pi_pos (a + u₁)
    simpa only [add_assoc] using this
  have hsum : Summable fun k : Fin g → ℤ => ‖thetaSummand X Y a b z k‖ := by
    simp_rw [hterm]
    exact hG.mul_right _
  have hN : thetaNorm X Y a b u₁ u₂ = ‖∑' k, thetaSummand X Y a b z k‖ * E := rfl
  rw [hN]
  calc ‖∑' k, thetaSummand X Y a b z k‖ * E
      ≤ (∑' k, ‖thetaSummand X Y a b z k‖) * E :=
        mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hsum) hEpos.le
    _ = ∑' k, ‖thetaSummand X Y a b z k‖ * E := (tsum_mul_right).symm
    _ = ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) := by
        congr 1; funext k
        rw [hterm, inv_mul_cancel_right₀ hEpos.ne']
end ThetaNormMajorant
end GroundTheory.Heights₂.Heights
