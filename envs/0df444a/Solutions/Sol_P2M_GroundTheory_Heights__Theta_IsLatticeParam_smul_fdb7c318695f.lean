-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_IsLatticeParam_smul_fdb7c318695f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:53:32.91523+00:00
-- url     : https://prove2.me/submissions/d0c3cb40-c471-4349-8042-78234b0d75b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassReducedParamsNonemptyPf
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_image_mul_latticeOf_7fca628f177e
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_span_denom_num_eq_6cb8a20bd333

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup Complex NumberField
open scoped Real MatrixGroups nonZeroDivisors
namespace GroundTheory.Heights₂.Theta
namespace IsLatticeParam
theorem _root_.solution {Λ : Set ℂ} {τ : ℍ} (h : IsLatticeParam Λ τ) (g : SL(2, ℤ)) :
    IsLatticeParam Λ (g • τ) := by
  obtain ⟨c, hc, hΛ⟩ := h
  set D : ℂ := (g 1 0 : ℂ) * τ + g 1 1 with hD
  have hD0 : D ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) τ
    simpa [UpperHalfPlane.denom, D] using this
  have hgτ : ((g • τ : ℍ) : ℂ) = ((g 0 0 : ℂ) * τ + g 0 1) / D := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [D]
  have key : (fun z => D * z) '' latticeOf ((g • τ : ℍ) : ℂ) = latticeOf (τ : ℂ) := by
    rw [image_mul_latticeOf, hgτ, mul_div_cancel₀ _ hD0, latticeOf, span_denom_num_eq]
  refine ⟨D⁻¹ * c, mul_ne_zero (inv_ne_zero hD0) hc, ?_⟩
  have : (fun z => D⁻¹ * c * z) '' Λ = (fun z => D⁻¹ * z) '' ((fun z => c * z) '' Λ) := by
    rw [Set.image_image]; simp [mul_assoc]
  rw [this, hΛ, ← key, Set.image_image]
  simp [inv_mul_cancel_left₀ hD0]
end IsLatticeParam
end GroundTheory.Heights₂.Theta
