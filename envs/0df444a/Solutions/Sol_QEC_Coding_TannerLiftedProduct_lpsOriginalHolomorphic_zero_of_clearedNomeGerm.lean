-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphic_zero_of_clearedNomeGerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:16:16.089953+00:00
-- url     : https://prove2.me/submissions/f110493f-30e3-47fa-82ba-2e358242c7fc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (F : LPSOriginalHolomorphicRing) (G : ℂ → ℂ) (B : ℕ)
    (hg : G =ᶠ[𝓝 (0 : ℂ)] 0)
    (hp : ∀ τ : ℍ, G (Function.Periodic.qParam 1 (τ : ℂ)) =
      (Function.Periodic.qParam 1 (τ : ℂ)) ^ B * F.val τ) :
    F = 0 := by
  obtain ⟨s, hs, hopen, h0⟩ := eventually_nhds_iff.mp hg
  obtain ⟨τ, hτ⟩ : ∃ τ : ℍ, Function.Periodic.qParam 1 (τ : ℂ) ∈ s :=
    ((UpperHalfPlane.qParam_tendsto_atImInfty
      (by norm_num : (0 : ℝ) < 1)).eventually
        (hopen.mem_nhds h0)).exists
  have hnear : ∀ᶠ z : ℍ in 𝓝 τ,
      Function.Periodic.qParam 1 (z : ℂ) ∈ s :=
    ((Function.Periodic.continuous_qParam.comp
      UpperHalfPlane.continuous_coe).continuousAt.tendsto).eventually
        (hopen.mem_nhds hτ)
  have hzero : ∀ᶠ z : ℍ in 𝓝 τ, F.val z = 0 := by
    filter_upwards [hnear] with z hz
    have h := hs _ hz
    change G (Function.Periodic.qParam 1 (z : ℂ)) = 0 at h
    rw [hp] at h
    exact (mul_eq_zero.mp h).resolve_left
      (pow_ne_zero _ (Function.Periodic.qParam_ne_zero _))
  apply Subtype.ext
  exact UpperHalfPlane.eq_zero_of_frequently F.property
    ((hzero.filter_mono nhdsWithin_le_nhds).frequently)
end QEC.Coding.TannerLiftedProduct
