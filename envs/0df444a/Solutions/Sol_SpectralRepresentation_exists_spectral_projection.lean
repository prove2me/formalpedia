-- Prove2me | solution 1 for SpectralRepresentation.exists_spectral_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:16:00.326804+00:00
-- url     : https://prove2.me/submissions/bb5d7099-c433-4539-9905-cd0c07d35e3e

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_BasicResults_Spectral_RealProjection
public import Definitions.Def_BasicResults_Spectral_Representation
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SpectralRepresentation_exists_spectral_projection_real
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
theorem _root_.solution (S : H₁ →L[𝕜] H₂) {c : ℝ} (hc0 : 0 ≤ c) :
    ∃ E : H₁ →L[𝕜] H₁,
      (∀ x : H₁, c * ‖E x‖ ≤ ‖S (E x)‖) ∧ ‖S.comp (1 - E)‖ ≤ c := by
  rcases subsingleton_or_nontrivial H₁ with hsub | hnt
  · have := hsub
    have hS0 : S = 0 := by ext x; rw [Subsingleton.elim x 0]; simp
    exact ⟨0, fun x => by simp, by rw [hS0]; simpa using hc0⟩
  · have := hnt
    let : InnerProductSpace ℝ H₁ := InnerProductSpace.rclikeToReal 𝕜 H₁
    let : InnerProductSpace ℝ H₂ := InnerProductSpace.rclikeToReal 𝕜 H₂
    -- The real adjoint of the realified operator equals the realified `𝕜`-adjoint.
    have hadj : adjoint (S.restrictScalars ℝ) = (adjoint S).restrictScalars ℝ := by
      symm
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      show re (inner 𝕜 (adjoint S x) y) = re (inner 𝕜 x (S y))
      rw [ContinuousLinearMap.adjoint_inner_left]
    obtain ⟨E₀, ha, hb, hcomm⟩ := exists_spectral_projection_real (S.restrictScalars ℝ) hc0
    -- `E₀` commutes with scalar multiplication, hence is `𝕜`-linear.
    have hsmul : ∀ (a : 𝕜) (x : H₁), E₀ (a • x) = a • E₀ x := by
      intro a x
      refine (hcomm ((a • (1 : H₁ →L[𝕜] H₁)).restrictScalars ℝ) (fun z => ?_) x).symm
      rw [hadj]
      simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
        smul_apply, one_apply_eq_self, map_smul]
    let Eₖ : H₁ →ₗ[𝕜] H₁ :=
      { toFun := E₀, map_add' := E₀.map_add, map_smul' := fun a x => hsmul a x }
    refine ⟨Eₖ.mkContinuous ‖E₀‖ fun x => E₀.le_opNorm x, fun x => ha x, ?_⟩
    have hcomp : (S.comp (1 - Eₖ.mkContinuous ‖E₀‖ fun x => E₀.le_opNorm x)).restrictScalars ℝ
        = (S.restrictScalars ℝ).comp (1 - E₀) := by
      ext x; rfl
    rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ), hcomp]
    exact hb
end SpectralRepresentation
