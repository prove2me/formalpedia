-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfConv.convComm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:29.960352+00:00
-- url     : https://prove2.me/submissions/8513ccfd-4df7-4de9-8ec4-c2996ec0fa82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandPairConvolution_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandPairConvolution_ConvComm
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_integral_comp_homeo
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_isInvInvariant_of_compact
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_isMulRightInvariant_of_compact
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_measurePreserving_anti
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_measurePreserving_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfConv
open MeasureTheory Measure
namespace PI.UnitaryGroupMassFormula.GelfConv
theorem _root_.solution : PI.UMultOne.ConvComm := by
  intro G _ _ _ _ _ _ _ _ μ _ H τ hc hm hi hconj f₁ f₂ _ _ hf₁ hf₂ z
  have := isMulRightInvariant_of_compact μ
  have := isInvInvariant_of_compact μ
  have h1 : τ 1 = 1 := by
    have := hm 1 1
    simp only [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hinv : ∀ x, τ x⁻¹ = (τ x)⁻¹ := fun x => by
    apply eq_inv_of_mul_eq_one_left
    rw [← hm, mul_inv_cancel, h1]

  have hτ₁ : ∀ x, f₁ (τ x) = f₁ x := fun x => by
    obtain ⟨h, hH, e⟩ := hconj x
    rw [e, hf₁ h hH]
  have hτ₂ : ∀ x, f₂ (τ x) = f₂ x := fun x => by
    obtain ⟨h, hH, e⟩ := hconj x
    rw [e, hf₂ h hH]

  have hF : ∀ h ∈ H, ∀ w, ∫ x, f₁ x * f₂ (x⁻¹ * (h * w * h⁻¹)) ∂μ = ∫ x, f₁ x * f₂ (x⁻¹ * w) ∂μ := by
    intro h hH w
    have e := integral_comp_homeo μ ((Homeomorph.mulLeft h).trans (Homeomorph.mulRight h⁻¹))
      (measurePreserving_conj μ h)
      (fun x => f₁ x * f₂ (x⁻¹ * (h * w * h⁻¹)))
    rw [← e]
    congr 1
    funext y
    simp only [Homeomorph.trans_apply, Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight]
    rw [hf₁ h hH]
    have : (h * y * h⁻¹)⁻¹ * (h * w * h⁻¹) = h * (y⁻¹ * w) * h⁻¹ := by group
    rw [this, hf₂ h hH]

  let eτ : G ≃ₜ G :=
    { toFun := τ, invFun := τ, left_inv := hi, right_inv := hi,
      continuous_toFun := hc, continuous_invFun := hc }
  have hτμ : MeasurePreserving eτ μ μ := measurePreserving_anti μ τ hc hm hi
  obtain ⟨h, hH, ez⟩ := hconj z

  have A : ∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ = ∫ x, f₁ x * f₂ (x⁻¹ * τ z) ∂μ := by
    rw [ez, hF h hH]

  have B : ∫ x, f₁ x * f₂ (x⁻¹ * τ z) ∂μ = ∫ y, f₁ y * f₂ (z * y⁻¹) ∂μ := by
    rw [← integral_comp_homeo μ eτ hτμ (fun x => f₁ x * f₂ (x⁻¹ * τ z))]
    congr 1
    funext y
    change f₁ (τ y) * f₂ ((τ y)⁻¹ * τ z) = f₁ y * f₂ (z * y⁻¹)
    rw [← hinv, ← hm, hτ₁, hτ₂]

  have C : ∫ y, f₁ y * f₂ (z * y⁻¹) ∂μ = ∫ x, f₂ x * f₁ (x⁻¹ * z) ∂μ := by
    have e1 := integral_mul_right_eq_self (μ := μ) (fun y => f₁ y * f₂ (z * y⁻¹)) z
    have e2 := integral_inv_eq_self (fun w => f₁ (w * z) * f₂ (z * (w * z)⁻¹)) μ
    rw [← e1, ← e2]
    congr 1
    funext w
    have : z * (w⁻¹ * z)⁻¹ = w := by group
    simp only [this, mul_comm]
  rw [A, B, C]
end PI.UnitaryGroupMassFormula.GelfConv
