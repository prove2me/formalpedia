-- Prove2me | solution 1 for SVD.sum_norm_sq_apply_le_of_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:06:34.180796+00:00
-- url     : https://prove2.me/submissions/5ae0649d-b8ee-4261-8985-b7bbda8dea41

module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_BasicResults_Spectral_Representation
public import Definitions.Def_BasicResults_SVD
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
omit [CompleteSpace H₁] [CompleteSpace H₂]
namespace SVD
theorem _root_.solution {S : H₁ →L[𝕜] H₂} {w : ℕ → H₁} {c : ℝ}
    (hS : ∀ x : H₁, ‖S x‖ ^ 2 = ∑' j, ‖(inner 𝕜 (w j) x : 𝕜)‖ ^ 2)
    (hc : ∀ J : Finset ℕ, ∑ j ∈ J, ‖w j‖ ^ 2 ≤ c)
    {u : ℕ → H₁} (hu : OrthonormalOrZero 𝕜 u) (s : Finset ℕ) :
    ∑ k ∈ s, ‖S (u k)‖ ^ 2 ≤ c := by
  have hw : Summable fun j => ‖w j‖ ^ 2 :=
    summable_of_sum_range_le (fun _ => by positivity) fun n => hc (Finset.range n)
  -- Each `j`-series is dominated by `∑ⱼ ‖wⱼ‖²`, because `‖uₖ‖ ≤ 1`.
  have hsummable : ∀ k, Summable fun j => ‖(inner 𝕜 (w j) (u k) : 𝕜)‖ ^ 2 := by
    intro k
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => ?_) hw
    have huk : ‖u k‖ ≤ 1 := by
      rcases hu.1 k with h | h
      · exact le_of_eq h
      · simp [h]
    calc ‖(inner 𝕜 (w j) (u k) : 𝕜)‖ ^ 2 ≤ (‖w j‖ * ‖u k‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
      _ ≤ ‖w j‖ ^ 2 := by
          rw [mul_pow]
          have h1 : ‖u k‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) huk 2
          calc ‖w j‖ ^ 2 * ‖u k‖ ^ 2 ≤ ‖w j‖ ^ 2 * 1 ^ 2 :=
                mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
            _ = ‖w j‖ ^ 2 := by ring
  -- Interchange the finite sum over `k` with the series over `j`.
  have hHS : HasSum (fun j => ∑ k ∈ s, ‖(inner 𝕜 (w j) (u k) : 𝕜)‖ ^ 2)
      (∑ k ∈ s, ‖S (u k)‖ ^ 2) := by
    refine hasSum_sum fun k _ => ?_
    rw [hS]
    exact (hsummable k).hasSum
  rw [← hHS.tsum_eq]
  refine hHS.summable.tsum_le_of_sum_le fun J => ?_
  calc ∑ j ∈ J, ∑ k ∈ s, ‖(inner 𝕜 (w j) (u k) : 𝕜)‖ ^ 2
      ≤ ∑ j ∈ J, ‖w j‖ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine le_trans (le_of_eq ?_) (hu.sum_inner_products_le (w j) s)
        exact Finset.sum_congr rfl fun k _ => by rw [norm_inner_symm]
    _ ≤ c := hc J
end SVD
