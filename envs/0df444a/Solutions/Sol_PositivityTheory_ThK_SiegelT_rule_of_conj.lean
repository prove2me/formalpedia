-- Prove2me | solution 1 for PositivityTheory.ThK.SiegelT.rule_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:04.20703+00:00
-- url     : https://prove2.me/submissions/ba6955d7-04e6-4ec6-a3da-24e85ae61f53

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β ν ν' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν]
  [Fintype ν'] [DecidableEq ν']
omit [DecidableEq α]
namespace PositivityTheory.ThK.SiegelT
theorem _root_.solution [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
    {κ : Type} [Fintype κ] {d : Darboux (symp c ξ JA JB) κ} {χ : Eˣ →* Circle} {C1 : Matrix β ν E} {C2 : Matrix β ν' E}
    {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)} (hs : IsSplitting C ψ d (actB c) om) (γ : UG c JB) (s : Matrix ν' ν E)
    (s' : Matrix ν ν' E) (h1 : s * s' = 1) (h2 : s' * s = 1) (hγ : ((γ : GL β E) : Matrix β β E) * C1 = C2 * s)
    (h : SiegelRule c C ψ ξ JA JB d χ C1 om) : SiegelRule c C ψ ξ JA JB d χ C2 om := by
  unfold SiegelRule at h ⊢
  intro l hl hinv p t hpt φ hφ
  have hC2 : C2 = ((γ : GL β E) : Matrix β β E) * C1 * s' := by
    rw [hγ, Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨t', ht'⟩ : ∃ t' : GL ν E, (t' : Matrix ν ν E) = s' * (t : Matrix ν' ν' E) * s :=
    ⟨⟨s' * (t : Matrix ν' ν' E) * s, s' * ((t⁻¹ : GL ν' E) : Matrix ν' ν' E) * s, by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc s s', h1, Matrix.one_mul, ← Matrix.mul_assoc (t : Matrix ν' ν' E), Units.mul_inv,
          Matrix.one_mul, h2], by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc s s', h1, Matrix.one_mul, ← Matrix.mul_assoc ((t⁻¹ : GL ν' E) : Matrix ν' ν' E),
          Units.inv_mul, Matrix.one_mul, h2]⟩, rfl⟩
  have hinvγ : (((γ : GL β E)⁻¹ : GL β E) : Matrix β β E) * ((γ : GL β E) : Matrix β β E) = 1 := Units.inv_mul _
  have hpt' : (((γ⁻¹ * p * γ : UG c JB) : GL β E) : Matrix β β E) * C1 = C1 * (t' : Matrix ν ν E) := by
    rw [ht']
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    calc _ = (((γ : GL β E)⁻¹ : GL β E) : Matrix β β E) * (((p : GL β E) : Matrix β β E) * C2) * s := by
            rw [Matrix.mul_assoc _ ((γ : GL β E) : Matrix β β E) C1, hγ]; simp only [Matrix.mul_assoc]
      _ = (((γ : GL β E)⁻¹ : GL β E) : Matrix β β E) * C2 * ((t : Matrix ν' ν' E) * s) := by
            rw [hpt]; simp only [Matrix.mul_assoc]
      _ = ((((γ : GL β E)⁻¹ : GL β E) : Matrix β β E) * ((γ : GL β E) : Matrix β β E)) * C1 *
            (s' * (t : Matrix ν' ν' E) * s) := by
            rw [hC2]; simp only [Matrix.mul_assoc]
      _ = C1 * (s' * (t : Matrix ν' ν' E) * s) := by rw [hinvγ, Matrix.one_mul]
  have hinv1 : ∀ (z : Matrix α ν E), ∀ φ ∈ C.sp κ, (l ∘ₗ om γ) (d.rho ψ (z * C1ᵀ) φ) = (l ∘ₗ om γ) φ := by
    intro z φ hφ
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs.impl γ (z * C1ᵀ) φ hφ]
    have hz : actB c γ (z * C1ᵀ) = (z * sᵀ) * C2ᵀ := by
      show z * C1ᵀ * (((γ : GL β E) : Matrix β β E))ᵀ = _
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hγ, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hz]
    exact hinv (z * sᵀ) _ (hs.pres γ φ hφ)
  have key := h (l ∘ₗ om γ) (hs.adm γ l hl) hinv1 (γ⁻¹ * p * γ) t' hpt' (om γ⁻¹ φ) (hs.pres γ⁻¹ φ hφ)
  have e1 : om γ (om (γ⁻¹ * p * γ) (om γ⁻¹ φ)) = om p φ := by
    have hg : γ * (γ⁻¹ * p * γ) * γ⁻¹ = p := by group
    conv_rhs => rw [← hg]
    simp only [map_mul, Module.End.mul_apply]
  have e2 : om γ (om γ⁻¹ φ) = φ := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have edet : Matrix.GeneralLinearGroup.det t' = Matrix.GeneralLinearGroup.det t := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, ht', Matrix.mul_assoc,
      Matrix.det_comm' h2 h1, Matrix.mul_assoc, h1, Matrix.mul_one]
  simp only [LinearMap.comp_apply] at key
  rw [e1, e2, edet] at key
  exact key
end PositivityTheory.ThK.SiegelT
