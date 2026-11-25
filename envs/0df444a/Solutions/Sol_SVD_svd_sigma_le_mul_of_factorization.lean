-- Prove2me | solution 1 for SVD.svd_sigma_le_mul_of_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:16:09.256384+00:00
-- url     : https://prove2.me/submissions/568d9f95-add3-443e-8def-4893d236308c

module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_BasicResults_Spectral_Representation
public import Definitions.Def_BasicResults_SVD
public import Theorems.Thm_SVD_svd_apply_left
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal
open SVD
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
variable {H₃ : Type u}
variable [NormedAddCommGroup H₃] [InnerProductSpace 𝕜 H₃] [CompleteSpace H₃]
omit [CompleteSpace H₁]
namespace SVD
theorem _root_.solution {T : H₁ →L[𝕜] H₃} {T₁ : H₁ →L[𝕜] H₂}
    {T₂ : H₂ →L[𝕜] H₃} (hfact : T = T₂.comp T₁) {σ : ℕ → ℝ} {u : ℕ → H₁} {v : ℕ → H₃}
    (hu : OrthonormalOrZero 𝕜 u) (hv : OrthonormalOrZero 𝕜 v)
    (hut : ∀ k, σ k ≠ 0 → u k ≠ 0) (hvt : ∀ k, σ k ≠ 0 → v k ≠ 0)
    (hsum : ∀ x, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (T x)) (k : ℕ) :
    σ k ≤ ‖ContinuousLinearMap.adjoint T₂ (v k)‖ * ‖T₁ (u k)‖ := by
  by_cases hk : σ k = 0
  · rw [hk]; positivity
  · have hvnorm : ‖v k‖ = 1 := (hv.1 k).resolve_right (hvt k hk)
    have hTu : T (u k) = (σ k : 𝕜) • v k := svd_apply_left hu hut hsum k
    have h1 : ((σ k : ℝ) : 𝕜) = inner 𝕜 (v k) (T (u k)) := by
      rw [hTu, inner_smul_right, inner_self_eq_norm_sq_to_K, hvnorm]
      push_cast; ring
    have h2 : (inner 𝕜 (v k) (T (u k)) : 𝕜)
        = inner 𝕜 (ContinuousLinearMap.adjoint T₂ (v k)) (T₁ (u k)) := by
      rw [hfact, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
    calc σ k = RCLike.re (((σ k : ℝ) : 𝕜)) := by simp
      _ = RCLike.re (inner 𝕜 (ContinuousLinearMap.adjoint T₂ (v k)) (T₁ (u k)) : 𝕜) := by
          rw [h1, h2]
      _ ≤ ‖ContinuousLinearMap.adjoint T₂ (v k)‖ * ‖T₁ (u k)‖ := re_inner_le_norm _ _
end SVD
