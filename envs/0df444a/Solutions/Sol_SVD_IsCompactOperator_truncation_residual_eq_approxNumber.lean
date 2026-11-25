-- Prove2me | solution 1 for SVD.IsCompactOperator.truncation_residual_eq_approxNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:42:37.324454+00:00
-- url     : https://prove2.me/submissions/1960d6c8-c4d4-456c-a4b9-7a28660299cc

module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_BasicResults_Spectral_Representation
public import Definitions.Def_BasicResults_SVD
public import Theorems.Thm_SVD_svd_sigma_eq_approx
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
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
omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- Pointwise formula for the truncated SVD. -/
private lemma svd_truncation_apply {σ : ℕ → ℝ} {u : ℕ → H₁} {v : ℕ → H₂}
    {L : H₁ →L[𝕜] H₂} {m : ℕ}
    (hLdef : L = ∑ k ∈ Finset.range m, (σ k : 𝕜) • (innerSL 𝕜 (u k)).smulRight (v k))
    (x : H₁) : L x = ∑ k ∈ Finset.range m, (σ k : 𝕜) • ((inner 𝕜 (u k) x : 𝕜) • v k) := by
  simp only [hLdef, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- **The truncated SVD has rank at most `m`.** Its range lies in the span of the
`m` vectors `v₀, …, v_{m-1}`. -/
private lemma svd_truncation_rank_le {σ : ℕ → ℝ} {u : ℕ → H₁} {v : ℕ → H₂}
    {L : H₁ →L[𝕜] H₂} {m : ℕ}
    (hLdef : L = ∑ k ∈ Finset.range m, (σ k : 𝕜) • (innerSL 𝕜 (u k)).smulRight (v k)) :
    L.rank ≤ (m : Cardinal) := by
  classical
  have hrange : LinearMap.range (L : H₁ →ₗ[𝕜] H₂) ≤
      Submodule.span 𝕜 (↑(Finset.image v (Finset.range m)) : Set H₂) := by
    intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [ContinuousLinearMap.coe_coe, svd_truncation_apply hLdef x]
    refine Submodule.sum_mem _ fun k hk =>
      Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem v hk))
  show Module.rank 𝕜 (LinearMap.range (L : H₁ →ₗ[𝕜] H₂)) ≤ (m : Cardinal)
  calc Module.rank 𝕜 (LinearMap.range (L : H₁ →ₗ[𝕜] H₂))
      ≤ Module.rank 𝕜 (Submodule.span 𝕜 (↑(Finset.image v (Finset.range m)) : Set H₂)) :=
        Submodule.rank_mono hrange
    _ ≤ #(↑(Finset.image v (Finset.range m)) : Set H₂) := rank_span_le _
    _ = ((Finset.image v (Finset.range m)).card : Cardinal) := Cardinal.mk_coe_finset
    _ ≤ ((Finset.range m).card : Cardinal) := by exact_mod_cast Finset.card_image_le
    _ = (m : Cardinal) := by rw [Finset.card_range]
omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- **Residual bound for the truncated SVD:** `‖S − Lₘ‖ ≤ σₘ`.

The residual is the orthonormal tail `∑_{k ≥ m} σₖ ⟪uₖ, x⟫ vₖ`. Every finite
tail-block has norm `≤ σₘ ‖x‖`: by orthonormality of the `vₖ` its square is
`∑ σₖ² |⟪uₖ, x⟫|² ≤ σₘ² ∑ |⟪uₖ, x⟫|² ≤ σₘ² ‖x‖²`, using that `σ` is antitone and
Bessel's inequality. Passing to the limit along the net of finite sets gives the
bound for the residual itself. -/
private lemma svd_truncation_residual_le {S : H₁ →L[𝕜] H₂} {σ : ℕ → ℝ} {u : ℕ → H₁}
    {v : ℕ → H₂} {L : H₁ →L[𝕜] H₂} {m : ℕ}
    (hσ0 : ∀ k, 0 ≤ σ k) (hσanti : Antitone σ) (hu : OrthonormalOrZero 𝕜 u)
    (hv : OrthonormalOrZero 𝕜 v) (hvt : ∀ k, σ k ≠ 0 → v k ≠ 0)
    (hsum : ∀ x, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (S x))
    (hLdef : L = ∑ k ∈ Finset.range m, (σ k : 𝕜) • (innerSL 𝕜 (u k)).smulRight (v k)) :
    ‖S - L‖ ≤ σ m := by
  refine ContinuousLinearMap.opNorm_le_bound _ (hσ0 m) fun x => ?_
  have hLg : L x = ∑ k ∈ Finset.range m, (((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) := by
    rw [svd_truncation_apply hLdef x]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]
  -- every finite tail-block has norm `≤ σ m · ‖x‖`.
  have hpartial : ∀ w : Finset ℕ, (∀ k ∈ w, m ≤ k) →
      ‖∑ k ∈ w, (((σ k : 𝕜) * inner 𝕜 (u k) x) • v k)‖ ≤ σ m * ‖x‖ := by
    intro w hw
    have hsq : ‖∑ k ∈ w, (((σ k : 𝕜) * inner 𝕜 (u k) x) • v k)‖ ^ 2
        ≤ (σ m * ‖x‖) ^ 2 := by
      rw [hv.norm_sum_smul_sq_of_support (fun k => (σ k : 𝕜) * inner 𝕜 (u k) x) w
            (fun k _ hvk => by
              have hσk : σ k = 0 := by by_contra h; exact hvt k h hvk
              rw [hσk]; simp)]
      calc ∑ k ∈ w, ‖(σ k : 𝕜) * inner 𝕜 (u k) x‖ ^ 2
          = ∑ k ∈ w, σ k ^ 2 * ‖inner 𝕜 (u k) x‖ ^ 2 := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [norm_mul, mul_pow, RCLike.norm_ofReal, abs_of_nonneg (hσ0 k)]
        _ ≤ ∑ k ∈ w, σ m ^ 2 * ‖inner 𝕜 (u k) x‖ ^ 2 :=
            Finset.sum_le_sum fun k hk =>
              mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (hσ0 k) (hσanti (hw k hk)) 2) (sq_nonneg _)
        _ = σ m ^ 2 * ∑ k ∈ w, ‖inner 𝕜 (u k) x‖ ^ 2 := by rw [Finset.mul_sum]
        _ ≤ σ m ^ 2 * ‖x‖ ^ 2 :=
            mul_le_mul_of_nonneg_left (hu.sum_inner_products_le x w) (sq_nonneg _)
        _ = (σ m * ‖x‖) ^ 2 := by rw [mul_pow]
    exact le_of_sq_le_sq hsq (mul_nonneg (hσ0 m) (norm_nonneg _))
  have htend0 : Tendsto
      (fun t : Finset ℕ => ∑ k ∈ t, (((σ k : 𝕜) * inner 𝕜 (u k) x) • v k))
      atTop (𝓝 (S x)) := hsum x
  have htend : Tendsto
      (fun t : Finset ℕ => ‖(∑ k ∈ t, (((σ k : 𝕜) * inner 𝕜 (u k) x) • v k)) - L x‖)
      atTop (𝓝 ‖S x - L x‖) := (htend0.sub_const (L x)).norm
  have hev : ∀ᶠ t : Finset ℕ in atTop,
      ‖(∑ k ∈ t, (((σ k : 𝕜) * inner 𝕜 (u k) x) • v k)) - L x‖ ≤ σ m * ‖x‖ := by
    rw [Filter.eventually_atTop]
    refine ⟨Finset.range m, fun t ht => ?_⟩
    have hsub : (∑ k ∈ t, (((σ k : 𝕜) * inner 𝕜 (u k) x) • v k)) - L x
        = ∑ k ∈ t \ Finset.range m, (((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) := by
      rw [hLg, ← Finset.sum_sdiff ht]; abel
    rw [hsub]
    exact hpartial _ fun k hk =>
      not_lt.mp (by simpa [Finset.mem_range] using (Finset.mem_sdiff.mp hk).2)
  have hbound : ‖S x - L x‖ ≤ σ m * ‖x‖ := le_of_tendsto htend hev
  rwa [sub_apply]
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
    ∃ L : H₁ →L[𝕜] H₂, L.rank ≤ (n : Cardinal) ∧
      ‖S - L‖ = SNumbers.approximationNumber S n := by
  classical
  obtain ⟨σ, u, v, hσ0, hσanti, hu, hv, hut, hvt, _hσlim, hsum⟩ := IsCompactOperator.SVD hS
  -- The truncated SVD `L x = Σ_{k<n} σₖ ⟨uₖ,x⟩ vₖ`, a sum of `n` rank-one maps.
  set L : H₁ →L[𝕜] H₂ :=
    ∑ k ∈ Finset.range n, (σ k : 𝕜) • (innerSL 𝕜 (u k)).smulRight (v k) with hLdef
  refine ⟨L, svd_truncation_rank_le hLdef, ?_⟩
  -- (i) `aₙ(S) ≤ ‖S - L‖` since `rank L ≤ n`.
  have hge : SNumbers.approximationNumber S n ≤ ‖S - L‖ :=
    SNumbers.approximationNumber_le_norm_sub (svd_truncation_rank_le hLdef)
  -- (ii) `‖S - L‖ ≤ σ n`: the residual is the orthonormal tail `∑_{k ≥ n} σₖ⟨uₖ,·⟩vₖ`.
  have hle : ‖S - L‖ ≤ σ n :=
    svd_truncation_residual_le hσ0 hσanti hu hv hvt hsum hLdef
  -- (iii) `σ n ≤ aₙ(S)`: the `m`-th singular value equals the `m`-th approximation
  -- number (`svd_sigma_eq_approx`).
  have hσa : σ n ≤ SNumbers.approximationNumber S n :=
    (svd_sigma_eq_approx hσ0 hσanti hu hv hut hvt hsum n).le
  -- Combine: `aₙ ≤ ‖S - L‖ ≤ σ n ≤ aₙ`.
  exact le_antisymm (hle.trans hσa) hge
end IsCompactOperator
end SVD
