-- Prove2me | solution 1 for SVD.svd_apply_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:20:12.150272+00:00
-- url     : https://prove2.me/submissions/cee78307-aed7-4069-bb37-76873a8a082d

module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_BasicResults_Spectral_Representation
public import Definitions.Def_BasicResults_SVD
public import Theorems.Thm_SVD_OrthonormalOrZero_smul_inner_eq
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
omit [CompleteSpace H₁] [CompleteSpace H₂]
namespace SVD
theorem _root_.solution {S : H₁ →L[𝕜] H₂} {σ : ℕ → ℝ} {u : ℕ → H₁} {v : ℕ → H₂}
    (hu : OrthonormalOrZero 𝕜 u) (htie : ∀ k, σ k ≠ 0 → u k ≠ 0)
    (hsum : ∀ x, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (S x)) (k : ℕ) :
    S (u k) = (σ k : 𝕜) • v k := by
  refine HasSum.unique (hsum (u k)) ?_
  have hfun : (fun j => ((σ j : 𝕜) * inner 𝕜 (u j) (u k)) • v j)
      = fun j => if j = k then (σ k : 𝕜) • v k else 0 := by
    funext j
    rw [hu.smul_inner_eq htie j k]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [hjk]
  rw [hfun]; exact hasSum_ite_eq k _
end SVD
