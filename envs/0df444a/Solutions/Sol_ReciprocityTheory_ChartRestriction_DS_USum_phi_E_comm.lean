-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.phi_E_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:40.778262+00:00
-- url     : https://prove2.me/submissions/f05173a5-1244-4a4b-982e-2efd73281907

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_InKRealSmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_inK_zM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_actM_zM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_phi_actM_inK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.DS
namespace USum
variable {n : ℕ} {ε : Fin n → Bool}
section Act
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
end Act
section Rep
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
  {V₁ : Submodule ℂ D₁} {V₂ : Submodule ℂ D₂}
private theorem eq_half_smul_sub_I_smul_combo {M : Type*} [AddCommGroup M] [Module ℂ M] (A B : M) :
    A = (1 / 2 : ℂ) • ((A - B) - Complex.I • (Complex.I • A - (-Complex.I) • B)) := by
  rw [smul_sub Complex.I, smul_smul, smul_smul, Complex.I_mul_I, mul_neg, Complex.I_mul_I, neg_neg,
    neg_one_smul, one_smul]
  rw [show (A - B) - (-A - B) = (2 : ℂ) • A by module, smul_smul]
  norm_num
end Rep
end USum
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.USum
variable {n : ℕ} {ε : Fin n → Bool}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
  {V₁ : Submodule ℂ D₁} {V₂ : Submodule ℂ D₂}
namespace ReciprocityTheory.ChartRestriction.DS.USum
theorem _root_.solution (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂)
    [FiniteDimensional ℂ V₁] (hst : IsKStableSub ε E₁ V₁)
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v) (φ : V₁ →ₗ[ℂ] V₂)
    (hφK : ∀ k ∈ Kset ε, ∀ (v : V₁) (w : V₁), ((w : D₁) : H₁) = σ₁ k ((v : D₁) : H₁) →
      (((φ w : V₂) : D₂) : H₂) = σ₂ k (((φ v : V₂) : D₂) : H₂))
    {a b : Fin n} (hab : ε a = ε b) (v : V₁) :
    E₂ a b ((φ v : V₂) : D₂) = ((φ ⟨E₁ a b v, hst a b hab _ v.2⟩ : V₂) : D₂) := by
  have hmem : ∀ c : ℂ, c • E₁ a b (v : D₁) - star c • E₁ b a (v : D₁) ∈ V₁ := fun c =>
    V₁.sub_mem (V₁.smul_mem _ (hst a b hab _ v.2)) (V₁.smul_mem _ (hst b a hab.symm _ v.2))
  let wc : ℂ → V₁ := fun c => ⟨c • E₁ a b (v : D₁) - star c • E₁ b a (v : D₁), hmem c⟩
  have key : ∀ c : ℂ, c • E₂ a b ((φ v : V₂) : D₂) - star c • E₂ b a ((φ v : V₂) : D₂) =
      ((φ (wc c) : V₂) : D₂) := by
    intro c
    have h := phi_actM_inK hD₁ hD₂ hVK₁ φ hφK (inK_zM hab c) v (wc c) (by rw [actM_zM]; rfl)
    rw [actM_zM, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply] at h
    exact Subtype.ext h
  have hw0 : (⟨E₁ a b v, hst a b hab _ v.2⟩ : V₁) = (1 / 2 : ℂ) • (wc 1 - Complex.I • wc Complex.I) := by
    apply Subtype.ext
    show E₁ a b (v : D₁) = (1 / 2 : ℂ) • (((1 : ℂ) • E₁ a b (v : D₁) - star (1 : ℂ) • E₁ b a (v : D₁)) -
      Complex.I • (Complex.I • E₁ a b (v : D₁) - star Complex.I • E₁ b a (v : D₁)))
    rw [star_one, one_smul, one_smul, Complex.star_def, Complex.conj_I]
    exact eq_half_smul_sub_I_smul_combo _ _
  rw [hw0, map_smul, map_sub, map_smul]
  show E₂ a b ((φ v : V₂) : D₂) =
    (1 / 2 : ℂ) • (((φ (wc 1) : V₂) : D₂) - Complex.I • ((φ (wc Complex.I) : V₂) : D₂))
  rw [← key 1, ← key Complex.I, star_one, one_smul, one_smul, Complex.star_def, Complex.conj_I]
  exact eq_half_smul_sub_I_smul_combo _ _
end ReciprocityTheory.ChartRestriction.DS.USum
