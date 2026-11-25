-- Prove2me | solution 1 for SVD.IsCompactOperator.diagonalFactorisation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:16:03.882479+00:00
-- url     : https://prove2.me/submissions/60290efb-0eed-447e-ae1b-52a5891c8922

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
public import Theorems.Thm_SVD_svd_sigma_eq_approx
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


section
@[expose] public section
universe u
open Filter Topology
open scoped Cardinal
namespace SVD
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
private lemma norm_sum_smul_sq {ι : Type*} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {w : ι → H} (hw : Orthonormal 𝕜 w) (c : ι → 𝕜)
    (s : Finset ι) :
    ‖∑ k ∈ s, c k • w k‖ ^ 2 = ∑ k ∈ s, ‖c k‖ ^ 2 := by
  rw [← @inner_self_eq_norm_sq 𝕜, hw.inner_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, RCLike.mul_conj]
  simp
section Factorization
variable {H₃ : Type u}
variable [NormedAddCommGroup H₃] [InnerProductSpace 𝕜 H₃] [CompleteSpace H₃]
end Factorization
end SVD
end
end

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
namespace SVD
namespace IsCompactOperator
theorem _root_.solution
    [Nontrivial H₁] [Nontrivial H₂]
    {S : H₁ →L[𝕜] H₂} (hS : IsCompactOperator S) (n : ℕ) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      ∀ k : Fin (n + 1),
        B (S (A (EuclideanSpace.single k (1 : 𝕜)))) =
          (SNumbers.approximationNumber S k : 𝕜) •
            EuclideanSpace.single k (1 : 𝕜) := by
  obtain ⟨σ, u, v, hσ0, hσanti, hu, hv, hut, hvt, _hσlim, hsum⟩ := IsCompactOperator.SVD hS
  have hσeq : ∀ m, σ m = SNumbers.approximationNumber S m :=
    svd_sigma_eq_approx hσ0 hσanti hu hv hut hvt hsum
  -- `A : eₖ ↦ uₖ` and `B : y ↦ ∑ ⟨vₖ,·⟩ eₖ`, both contractions.
  set A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁ :=
    ∑ k : Fin (n + 1), (innerSL 𝕜 (EuclideanSpace.single k (1 : 𝕜))).smulRight (u k)
    with hAdef
  set B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
    ∑ k : Fin (n + 1), (innerSL 𝕜 (v k)).smulRight (EuclideanSpace.single k (1 : 𝕜))
    with hBdef
  refine ⟨A, B, ?_, ?_, ?_⟩
  · -- `‖A‖ ≤ 1`: `‖A x‖² = ∑ ‖xₖ‖²‖uₖ‖² ≤ ∑ ‖xₖ‖² = ‖x‖²`.
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    have hAx : A x = ∑ k : Fin (n + 1), (x k) • u k := by
      simp only [hAdef, sum_apply, ContinuousLinearMap.smulRight_apply,
        innerSL_apply_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
    have hsq : ‖A x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      have h1 : ‖A x‖ ^ 2 = ∑ k : Fin (n + 1), ‖x k‖ ^ 2 * ‖u (k : ℕ)‖ ^ 2 := by
        rw [hAx]
        exact (hu.comp (f := (Fin.val : Fin (n + 1) → ℕ)) Fin.val_injective).norm_sum_smul_sq
          (fun k => x k) Finset.univ
      have h2 : ‖x‖ ^ 2 = ∑ k : Fin (n + 1), ‖x k‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      rw [h1, h2]
      refine Finset.sum_le_sum fun k _ => ?_
      rcases hu.1 (k : ℕ) with hk1 | hk0
      · rw [hk1, one_pow, mul_one]
      · rw [hk0, norm_zero]
        have h0 : ‖x k‖ ^ 2 * (0 : ℝ) ^ 2 = 0 := by ring
        rw [h0]; exact sq_nonneg _
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  · -- `‖B‖ ≤ 1`: Bessel's inequality.
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    rw [one_mul]
    have hBy : B y =
        ∑ k : Fin (n + 1), (inner 𝕜 (v k) y : 𝕜) • EuclideanSpace.single k (1 : 𝕜) := by
      simp only [hBdef, sum_apply, ContinuousLinearMap.smulRight_apply,
        innerSL_apply_apply]
    have hsq : ‖B y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      have h1 : ‖B y‖ ^ 2 = ∑ k : Fin (n + 1), ‖inner 𝕜 (v k) y‖ ^ 2 := by
        rw [hBy]
        exact norm_sum_smul_sq
          (EuclideanSpace.orthonormal_single :
            Orthonormal 𝕜 (fun i : Fin (n + 1) => EuclideanSpace.single i (1 : 𝕜)))
          (fun k => inner 𝕜 (v k) y) Finset.univ
      rw [h1]
      exact (hv.comp (f := (Fin.val : Fin (n + 1) → ℕ)) Fin.val_injective).sum_inner_products_le
        y Finset.univ
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  · -- Diagonalisation: `B (S (A eₖ)) = B (σₖ vₖ) = σₖ eₖ = aₖ eₖ`.
    intro k
    have hAk : A (EuclideanSpace.single k (1 : 𝕜)) = u k := by
      rw [hAdef, sum_apply]
      refine (Finset.sum_eq_single k ?_ ?_).trans ?_
      · intro j _ hjk
        simp [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
          EuclideanSpace.inner_single_left, hjk]
      · intro h; exact absurd (Finset.mem_univ k) h
      · simp [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [hAk, svd_apply_left hu hut hsum (k : ℕ), map_smul, ← hσeq (k : ℕ)]
    by_cases hσk : σ (k : ℕ) = 0
    · rw [hσk]; simp
    · have hvk : v (k : ℕ) ≠ 0 := hvt (k : ℕ) hσk
      have hBvk : B (v (k : ℕ)) = EuclideanSpace.single k (1 : 𝕜) := by
        rw [hBdef, sum_apply]
        refine (Finset.sum_eq_single k ?_ ?_).trans ?_
        · intro j _ hjk
          rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hv.inner_eq ↑j ↑k,
            if_neg (Fin.val_injective.ne hjk), zero_smul]
        · intro h; exact absurd (Finset.mem_univ k) h
        · rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hv.inner_eq ↑k ↑k,
            if_pos rfl, (hv.1 ↑k).resolve_right hvk]; norm_num
      rw [hBvk]
end IsCompactOperator
end SVD
