-- Prove2me | solution 1 for SVD.exists_scalar_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:18:03.723733+00:00
-- url     : https://prove2.me/submissions/e45cd887-1779-4ac0-a31e-eacb4bd96cf5

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
public import Theorems.Thm_SpectralRepresentation_exists_lowerBound_subspace
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
namespace SVD
theorem _root_.solution
    (S : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c < SNumbers.approximationNumber S n) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      B.comp (S.comp A) =
        (c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
  classical
  obtain ⟨M, hMfd, hMrank, hMlb⟩ := SpectralRepresentation.exists_lowerBound_subspace S n hc0 hc
  -- `A`: isometric embedding of `ℓ₂ⁿ⁺¹` onto `M`.
  let e : OrthonormalBasis (Fin (n + 1)) 𝕜 M := (stdOrthonormalBasis 𝕜 M).reindex (finCongr hMrank)
  set A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁ :=
    M.subtypeL.comp e.repr.symm.toContinuousLinearMap with hAdef
  have hAisom : ∀ x, ‖A x‖ = ‖x‖ := fun x => by
    rw [hAdef, ContinuousLinearMap.comp_apply]; exact e.repr.symm.norm_map x
  have hAmem : ∀ x, A x ∈ M := fun x => by
    rw [hAdef, ContinuousLinearMap.comp_apply]; exact (e.repr.symm x).2
  have hA1 : ‖A‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [hAisom, one_mul]
  set T : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₂ := S.comp A with hTdef
  have hTlb : ∀ x, c * ‖x‖ ≤ ‖T x‖ := fun x => by
    rw [hTdef, ContinuousLinearMap.comp_apply, ← hAisom x]; exact hMlb (A x) (hAmem x)
  rcases eq_or_lt_of_le hc0 with hc0' | hcpos
  · -- `c = 0`: take `B = 0`.
    subst hc0'
    exact ⟨A, 0, hA1, by simp, by ext v; simp⟩
  · -- `c > 0`: `B = c · (T* T)⁻¹ ∘ T*`.
    set G : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
      (ContinuousLinearMap.adjoint T).comp T with hGdef
    have hGinner : ∀ x, inner 𝕜 (G x) x = inner 𝕜 (T x) (T x) := fun x => by
      rw [hGdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
    have hGunit : IsUnit G :=
      ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map G
        (c := ⟨c ^ 2, sq_nonneg c⟩) (by exact_mod_cast pow_pos hcpos 2) fun x => by
        have hb : ‖x‖ ^ 2 * c ^ 2 ≤ ‖inner 𝕜 (G x) x‖ := by
          calc ‖x‖ ^ 2 * c ^ 2 ≤ ‖T x‖ ^ 2 := by
                nlinarith [hTlb x, norm_nonneg (T x), mul_nonneg hc0 (norm_nonneg x)]
            _ = RCLike.re (inner 𝕜 (G x) x) := by rw [hGinner x, inner_self_eq_norm_sq]
            _ ≤ ‖inner 𝕜 (G x) x‖ := RCLike.re_le_norm _
        exact hb
    set Ginv : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
      Ring.inverse G with hGinvdef
    have hGinvG : Ginv.comp G = 1 := by rw [hGinvdef]; exact Ring.inverse_mul_cancel G hGunit
    have hGGinv : G.comp Ginv = 1 := by rw [hGinvdef]; exact Ring.mul_inverse_cancel G hGunit
    set B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) := (c : 𝕜) • Ginv.comp (ContinuousLinearMap.adjoint T) with hBdef
    refine ⟨A, B, hA1, ?_, ?_⟩
    · -- `‖B‖ ≤ 1`.
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
      rw [one_mul, hBdef, smul_apply, ContinuousLinearMap.comp_apply,
        norm_smul, RCLike.norm_ofReal, abs_of_nonneg hc0]
      set z := Ginv ((ContinuousLinearMap.adjoint T) y) with hz
      have hGz : G z = (ContinuousLinearMap.adjoint T) y := by
        rw [hz, ← ContinuousLinearMap.comp_apply, hGGinv, one_apply_eq_self]
      have hTz : ‖T z‖ ^ 2 = RCLike.re (inner 𝕜 (T z) y) := by
        have h1 : (inner 𝕜 (T z) (T z) : 𝕜) = inner 𝕜 (T z) y := by
          rw [← ContinuousLinearMap.adjoint_inner_right T z (T z),
            show (ContinuousLinearMap.adjoint T) (T z) = G z by
              rw [hGdef]; exact (ContinuousLinearMap.comp_apply _ _ _).symm,
            hGz, ContinuousLinearMap.adjoint_inner_right T z y]
        rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), h1]
      have hTzy : ‖T z‖ ≤ ‖y‖ := by
        rcases eq_or_lt_of_le (norm_nonneg (T z)) with h0 | hpos
        · linarith [norm_nonneg y, h0.symm]
        · have hle : ‖T z‖ ^ 2 ≤ ‖T z‖ * ‖y‖ := by
            rw [hTz]; exact (RCLike.re_le_norm _).trans (norm_inner_le_norm (𝕜 := 𝕜) (T z) y)
          nlinarith [hpos]
      nlinarith [hTlb z, hTzy, mul_nonneg hc0 (norm_nonneg z)]
    · -- `B ∘ S ∘ A = c • id`.
      rw [hBdef, ← hTdef, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc,
        ← hGdef, hGinvG, ContinuousLinearMap.one_def]
end SVD
