-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_archDualNorm_pos_3023062927e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:39.573961+00:00
-- url     : https://prove2.me/submissions/5a3a108b-6150-4758-a77f-dff32478a5f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfPoint

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
open MvPolynomial NumberField ComplexAt TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.HeightOfPointAlt
variable {K : Type*} [Field K] [NumberField K]
variable {F : Type*} [Field F] [NumberField F] [Algebra F K]
variable {W : Type*} [AddCommGroup W] [Module (𝓞 F) W] [Module.Finite (𝓞 F) W]
  [Module.Projective (𝓞 F) W]
namespace GroundTheory.Heights₂.Heights.HeightOfPointAlt
theorem _root_.solution (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) (x : W)
    (hx : yv x ≠ 0) : 0 < archDualNorm h τ yv := by
  set σ := τ.comp (algebraMap F K)
  let φ : FibreSpace h σ →ₗ[ℂ] ℂ := (ofComplex σ).symm.toLinearMap ∘ₗ archLinear τ yv ∘ₗ
    (FibreSpace.equiv h σ).symm.toLinearMap
  have hφ : ∀ ξ, φ ξ = (ofComplex σ).symm (archFunctional τ yv ((FibreSpace.equiv h σ).symm ξ)) :=
    fun _ => rfl
  let φc := LinearMap.toContinuousLinearMap φ
  have hbdd : BddAbove (Set.range fun ξ : {ξ : FibreSpace h σ // ‖ξ‖ ≤ 1} =>
      ‖(ofComplex σ).symm (archFunctional τ yv ((FibreSpace.equiv h σ).symm ξ))‖) := by
    refine ⟨‖φc‖, ?_⟩
    rintro _ ⟨ξ, rfl⟩
    show ‖φ ξ‖ ≤ _
    calc ‖φ ξ‖ = ‖φc ξ‖ := rfl
      _ ≤ ‖φc‖ * ‖(ξ : FibreSpace h σ)‖ := φc.le_opNorm _
      _ ≤ ‖φc‖ * 1 := mul_le_mul_of_nonneg_left ξ.2 (norm_nonneg φc)
      _ = ‖φc‖ := mul_one _
  set ξ₀ : FibreSpace h σ := FibreSpace.equiv h σ ((1 : ComplexAt σ) ⊗ₜ x)
  have hξ₀ : φ ξ₀ = τ (yv x) := by
    rw [hφ]
    simp only [ξ₀, LinearEquiv.symm_apply_apply, archFunctional, TensorProduct.lift.tmul,
      LinearMap.mk₂_apply, one_mul]
    rfl
  have hne : ξ₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hξ₀
    exact (map_ne_zero τ).mpr hx hξ₀.symm
  set ξ₁ : FibreSpace h σ := ((‖ξ₀‖ : ℂ)⁻¹) • ξ₀
  have hξ₁ : ‖ξ₁‖ ≤ 1 := le_of_eq (norm_smul_inv_norm hne)
  have hφ₁ : φ ξ₁ ≠ 0 := by
    rw [map_smul, hξ₀, smul_eq_mul]
    refine mul_ne_zero (inv_ne_zero ?_) ((map_ne_zero τ).mpr hx)
    exact_mod_cast (norm_ne_zero_iff.mpr hne)
  calc (0 : ℝ) < ‖φ ξ₁‖ := norm_pos_iff.mpr hφ₁
    _ ≤ archDualNorm h τ yv := by
      rw [hφ]
      exact le_ciSup hbdd ⟨ξ₁, hξ₁⟩
end GroundTheory.Heights₂.Heights.HeightOfPointAlt
