-- Prove2me | solution 1 for SpectralRepresentation.exists_spectral_projection_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:12:22.939991+00:00
-- url     : https://prove2.me/submissions/c8328a28-4179-42d9-a5aa-cf08e223629b

module
public import Definitions.Def_BasicResults_Spectral_Complexification
public import Definitions.Def_BasicResults_Spectral_Projection
public import Definitions.Def_BasicResults_Spectral_RealProjection
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_conj_eq_self_iff
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SpectralRepresentation_exists_spectral_projection_complex
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify



set_option autoImplicit true
@[expose] public section
public section
open SNumbers.Complexification ContinuousLinearMap
open SpectralRepresentation
variable {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
namespace SpectralRepresentation
theorem _root_.solution [Nontrivial H₁]
    (S : H₁ →L[ℝ] H₂) {c : ℝ} (hc0 : 0 ≤ c) :
    ∃ E : H₁ →L[ℝ] H₁,
      (∀ x : H₁, c * ‖E x‖ ≤ ‖S (E x)‖) ∧ ‖S.comp (1 - E)‖ ≤ c ∧
        ∀ K : H₁ →L[ℝ] H₁, (∀ x, K (((adjoint S).comp S) x) = ((adjoint S).comp S) (K x)) →
          ∀ x, K (E x) = E (K x) := by
  obtain ⟨Eℂ, hEa, hEb, hEcomm⟩ := exists_spectral_projection_complex (complexify S) hc0
  -- Conjugation commutes with `P = Sℂ* Sℂ` (because `P` is a complexification), hence with `Eℂ`.
  have hEconj : ∀ u, conj (Eℂ u) = Eℂ (conj u) := by
    have h := hEcomm conjL fun w => by
      simp only [conjL_apply, ContinuousLinearMap.comp_apply, adjoint_complexify, complexify_conj]
    simpa only [conjL_apply] using h
  -- The restricted real operator `E x = re (Eℂ (x + i·0))`.
  set E : H₁ →L[ℝ] H₁ :=
    fstL.comp ((Eℂ.restrictScalars ℝ).comp ofRealLi.toContinuousLinearMap) with hEdef
  have hEx : ∀ x, E x = (Eℂ (ofReal x)).1 := fun _ => rfl
  -- `Eℂ` preserves the real subspace, so `Eℂ (x + i·0) = (E x) + i·0`.
  have hEofReal : ∀ x, Eℂ (ofReal x) = ofReal (E x) := by
    intro x
    have hfix : conj (Eℂ (ofReal x)) = Eℂ (ofReal x) := by rw [hEconj, conj_ofReal]
    obtain ⟨z, hz⟩ := (conj_eq_self_iff _).mp hfix
    rw [hz, hEx, hz, ofReal_fst]
  refine ⟨E, ?_, ?_, ?_⟩
  · -- bound (a)
    intro x
    have h := hEa (ofReal x)
    simp only [hEofReal x, complexify_ofReal, norm_ofReal] at h
    exact h
  · -- bound (b)
    refine ContinuousLinearMap.opNorm_le_bound _ hc0 fun y => ?_
    have key : ((complexify S).comp (1 - Eℂ)) (ofReal y) = ofReal (S ((1 - E) y)) := by
      rw [ContinuousLinearMap.comp_apply, sub_apply,
        one_apply_eq_self, hEofReal y, ← ofReal_sub, complexify_ofReal,
        sub_apply, one_apply_eq_self]
    calc ‖S ((1 - E) y)‖ = ‖((complexify S).comp (1 - Eℂ)) (ofReal y)‖ := by rw [key, norm_ofReal]
      _ ≤ ‖(complexify S).comp (1 - Eℂ)‖ * ‖ofReal y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖y‖ := by rw [norm_ofReal]; exact mul_le_mul_of_nonneg_right hEb (norm_nonneg y)
  · -- commutation: `E` commutes with any `K` commuting with `S* S`.
    intro K hK x
    -- `complexify K` commutes with `Pℂ = Sℂ* Sℂ` (componentwise, from `hK`).
    have hKcomm : ∀ u, (complexify K) (((adjoint (complexify S)).comp (complexify S)) u)
        = ((adjoint (complexify S)).comp (complexify S)) ((complexify K) u) := by
      intro u
      refine Prod.ext ?_ ?_ <;>
        simp only [ContinuousLinearMap.comp_apply, adjoint_complexify, complexify_fst,
          complexify_snd]
      · exact hK u.1
      · exact hK u.2
    have hEKcomm : ∀ u, complexify K (Eℂ u) = Eℂ (complexify K u) :=
      hEcomm ((complexify K).restrictScalars ℝ) hKcomm
    calc K (E x) = K ((Eℂ (ofReal x)).1) := by rw [hEx]
      _ = (complexify K (Eℂ (ofReal x))).1 := (complexify_fst K _).symm
      _ = (Eℂ (complexify K (ofReal x))).1 := by rw [hEKcomm]
      _ = (Eℂ (ofReal (K x))).1 := by rw [complexify_ofReal]
      _ = E (K x) := (hEx (K x)).symm
end SpectralRepresentation
