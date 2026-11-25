-- Prove2me | solution 1 for SVD.svd_sigma_eq_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:29:57.117653+00:00
-- url     : https://prove2.me/submissions/71b35887-b0bc-4def-abde-4f6b6099cd15

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
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
public import Theorems.Thm_SNumbers_approximationNumber_nonneg
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_gainOnSubspace_le_norm
public import Theorems.Thm_SNumbers_isStrictSNumberSequence_bernsteinNumber
public import Theorems.Thm_SNumbers_le_gainOnSubspace
public import Theorems.Thm_SNumbers_sn_le_approximationNumber
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
omit [CompleteSpace H₁] [CompleteSpace H₂]
namespace SVD
theorem _root_.solution {S : H₁ →L[𝕜] H₂} {σ : ℕ → ℝ} {u : ℕ → H₁}
    {v : ℕ → H₂} (hσ0 : ∀ k, 0 ≤ σ k) (hσanti : Antitone σ) (hu : OrthonormalOrZero 𝕜 u)
    (hv : OrthonormalOrZero 𝕜 v) (hut : ∀ k, σ k ≠ 0 → u k ≠ 0) (hvt : ∀ k, σ k ≠ 0 → v k ≠ 0)
    (hsum : ∀ x, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (S x)) (m : ℕ) :
    σ m = SNumbers.approximationNumber S m := by
  classical
  set L : H₁ →L[𝕜] H₂ :=
    ∑ k ∈ Finset.range m, (σ k : 𝕜) • (innerSL 𝕜 (u k)).smulRight (v k) with hLdef
  -- `aₘ(S) ≤ ‖S - Lₘ‖ ≤ σₘ` for the truncation `Lₘ`.
  have hge : SNumbers.approximationNumber S m ≤ ‖S - L‖ :=
    SNumbers.approximationNumber_le_norm_sub (svd_truncation_rank_le hLdef)
  have hle : ‖S - L‖ ≤ σ m :=
    svd_truncation_residual_le hσ0 hσanti hu hv hvt hsum hLdef
  have hσa : σ m ≤ SNumbers.approximationNumber S m := by
    by_cases hσm : σ m = 0
    · rw [hσm]; exact SNumbers.approximationNumber_nonneg S m
    · have hσpos : 0 < σ m := lt_of_le_of_ne (hσ0 m) (Ne.symm hσm)
      have hσi : ∀ i : Fin (m + 1), σ (i : ℕ) ≠ 0 := fun i =>
        ne_of_gt (lt_of_lt_of_le hσpos (hσanti (Fin.is_le i)))
      have he_orth : Orthonormal 𝕜 (fun i : Fin (m + 1) => u i) := by
        rw [orthonormal_iff_ite]
        intro i j
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl, inner_self_eq_norm_sq_to_K,
            (hu.1 (i : ℕ)).resolve_right (hut (i : ℕ) (hσi i))]; norm_num
        · rw [if_neg hij]; exact hu.2 (Fin.val_injective.ne hij)
      have hv_orth : Orthonormal 𝕜 (fun i : Fin (m + 1) => v i) := by
        rw [orthonormal_iff_ite]
        intro i j
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl, inner_self_eq_norm_sq_to_K,
            (hv.1 (i : ℕ)).resolve_right (hvt (i : ℕ) (hσi i))]; norm_num
        · rw [if_neg hij]; exact hv.2 (Fin.val_injective.ne hij)
      set M : Submodule 𝕜 H₁ :=
        Submodule.span 𝕜 (Set.range (fun i : Fin (m + 1) => u i)) with hMdef
      have he_li : LinearIndependent 𝕜 (fun i : Fin (m + 1) => u i) :=
        he_orth.linearIndependent
      have hMrank : Module.rank 𝕜 M = ((m + 1 : ℕ) : Cardinal) := by
        classical
        have : Fintype (Set.range (fun i : Fin (m + 1) => u i)) := Set.fintypeRange _
        rw [hMdef, rank_span he_li, Cardinal.mk_fintype,
          Set.card_range_of_injective he_li.injective, Fintype.card_fin]
      have hMne : M ≠ ⊥ := by
        intro h; rw [h, rank_bot] at hMrank
        exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)) hMrank.symm
      have hgain : σ m ≤ SNumbers.gainOnSubspace S M := by
        refine SNumbers.le_gainOnSubspace hMne fun x hxM hxne => ?_
        rw [le_div_iff₀ (norm_pos_iff.mpr hxne)]
        obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hxM
        have hxnorm : ‖x‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
          rw [← ha]; exact norm_sum_smul_sq he_orth a Finset.univ
        have hSx : S x = ∑ i : Fin (m + 1), (a i * (σ (i : ℕ) : 𝕜)) • v i := by
          rw [← ha, map_sum]
          exact Finset.sum_congr rfl fun i _ => by
            simp only [map_smul, svd_apply_left hu hut hsum, smul_smul]
        have hSxnorm : ‖S x‖ ^ 2 = ∑ i, ‖a i * (σ (i : ℕ) : 𝕜)‖ ^ 2 := by
          rw [hSx]; exact norm_sum_smul_sq hv_orth _ Finset.univ
        have hkey : (σ m) ^ 2 * ‖x‖ ^ 2 ≤ ‖S x‖ ^ 2 := by
          rw [hxnorm, hSxnorm, Finset.mul_sum]
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, mul_pow, RCLike.norm_ofReal, abs_of_nonneg (hσ0 _),
            mul_comm (‖a i‖ ^ 2)]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (hσ0 m) (hσanti (Fin.is_le i)) 2) (sq_nonneg _)
        have hkey2 : (σ m * ‖x‖) ^ 2 ≤ ‖S x‖ ^ 2 := by rw [mul_pow]; exact hkey
        exact le_of_sq_le_sq hkey2 (norm_nonneg _)
      have hbern : σ m ≤ SNumbers.bernsteinNumber S m := by
        refine hgain.trans ?_
        unfold SNumbers.bernsteinNumber
        refine le_csSup ⟨‖S‖, ?_⟩ ⟨M, hMrank, rfl⟩
        rintro r ⟨M', _, rfl⟩
        exact SNumbers.gainOnSubspace_le_norm S M'
      exact hbern.trans (SNumbers.sn_le_approximationNumber
        SNumbers.isStrictSNumberSequence_bernsteinNumber.toIsSNumberSequence S m)
  exact le_antisymm hσa (hge.trans hle)
end SVD
