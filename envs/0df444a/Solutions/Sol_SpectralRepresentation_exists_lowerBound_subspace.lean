-- Prove2me | solution 1 for SpectralRepresentation.exists_lowerBound_subspace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:17:09.248134+00:00
-- url     : https://prove2.me/submissions/dc86ab95-c615-48cc-a0e9-e0855ec1e5c8

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_BasicResults_Spectral_RealProjection
public import Definitions.Def_BasicResults_Spectral_Representation
public import Theorems.Thm_SpectralRepresentation_exists_spectral_projection
public import Theorems.Thm_ContinuousLinearMap_rank_comp_comp_le
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm



set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap SNumbers.Complexification RCLike
universe u
open SpectralRepresentation
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
namespace SpectralRepresentation
theorem _root_.solution
    (S : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c)
    (hca : c < SNumbers.approximationNumber S n) :
    ∃ M : Submodule 𝕜 H₁, FiniteDimensional 𝕜 M ∧
      Module.finrank 𝕜 M = n + 1 ∧
      ∀ x ∈ M, c * ‖x‖ ≤ ‖S x‖ := by
  classical
  obtain ⟨E, hElb, hEub⟩ := exists_spectral_projection S hc0
  set V : Submodule 𝕜 H₁ := LinearMap.range (E : H₁ →ₗ[𝕜] H₁) with hVdef
  -- `S` is bounded below by `c` on the range of `E`: every element is `E y`.
  have hbound : ∀ x ∈ V, c * ‖x‖ ≤ ‖S x‖ := by
    intro x hx
    obtain ⟨y, hy⟩ := hx
    have hEy : E y = x := hy
    have := hElb y; rwa [hEy] at this
  -- `S ∘ (1 - E)` is small, so `S ∘ E` cannot be low rank.
  have hSE : S - S.comp E = S.comp (1 - E) := by
    ext x
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      one_apply_eq_self, map_sub]
  have hrank_se : (S.comp E).rank ≤ E.rank := by
    have h := ContinuousLinearMap.rank_comp_comp_le (ContinuousLinearMap.id 𝕜 H₁) E S
    rwa [ContinuousLinearMap.comp_id] at h
  -- The range of `E` has dimension at least `n + 1`.
  have hrankV : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank 𝕜 V := by
    by_contra hcon
    rw [not_le] at hcon
    have hEn : E.rank ≤ (n : Cardinal) := by
      apply Order.lt_succ_iff.mp
      have hcast : ((n + 1 : ℕ) : Cardinal) = (n : Cardinal) + 1 := by push_cast; ring
      rw [Cardinal.succ_natCast, ← hcast]
      exact hcon
    have hbad : SNumbers.approximationNumber S n ≤ c :=
      le_trans (SNumbers.approximationNumber_le_norm_sub (le_trans hrank_se hEn))
        (by rw [hSE]; exact hEub)
    exact absurd hca (not_lt.mpr hbad)
  -- Extract `n + 1` independent vectors of `V`; their span is the subspace `M`.
  obtain ⟨v, hv⟩ := Module.le_rank_iff.mp hrankV
  set w : Fin (n + 1) → H₁ := fun i => (v i : H₁) with hwdef
  have hw : LinearIndependent 𝕜 w := hv.map' V.subtype (Submodule.ker_subtype V)
  refine ⟨Submodule.span 𝕜 (Set.range w),
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range w), ?_, ?_⟩
  · rw [finrank_span_eq_card hw, Fintype.card_fin]
  · intro x hx
    refine hbound x ?_
    refine (Submodule.span_le.mpr ?_) hx
    rintro _ ⟨i, rfl⟩
    exact (v i).2
end SpectralRepresentation
