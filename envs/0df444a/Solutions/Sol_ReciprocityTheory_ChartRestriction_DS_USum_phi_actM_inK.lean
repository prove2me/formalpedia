-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.phi_actM_inK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:14:28.847999+00:00
-- url     : https://prove2.me/submissions/49963caf-7fc5-4a17-bb9d-46f7ce5379eb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_InKRealSmul
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
private theorem exp_smul_mem_Kset_of_skew_of_commute_Jm {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := by
  obtain ⟨hG, hC⟩ := hX
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hskew : Xᴴ = -X := by
    have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
      rw [hC]
      exact eq_neg_of_add_eq_zero_left hG
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -(X * Jm ε) * Jm ε := by rw [h1]
      _ = -X := by rw [Matrix.neg_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have ht : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  have hY : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
    rw [Matrix.conjTranspose_smul, hskew, ht, smul_neg]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hY,
      ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl ((t : ℂ) • X))), add_neg_cancel,
      NormedSpace.exp_zero]
  · letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    have hc : Commute ((t : ℂ) • X) (Jm ε) := by
      show (t : ℂ) • X * Jm ε = Jm ε * ((t : ℂ) • X)
      rw [Matrix.smul_mul, Matrix.mul_smul, hC]
    exact hc.exp_left.eq
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
    [FiniteDimensional ℂ V₁]
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v) (φ : V₁ →ₗ[ℂ] V₂)
    (hφK : ∀ k ∈ Kset ε, ∀ (v : V₁) (w : V₁), ((w : D₁) : H₁) = σ₁ k ((v : D₁) : H₁) →
      (((φ w : V₂) : D₂) : H₂) = σ₂ k (((φ v : V₂) : D₂) : H₂))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (v u : V₁) (hu : (u : D₁) = actM E₁ X v) :
    ((actM E₂ X ((φ v : V₂) : D₂) : D₂) : H₂) = (((φ u : V₂) : D₂) : H₂) := by
  classical
  have hk : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := fun t => exp_smul_mem_Kset_of_skew_of_commute_Jm hX t
  choose w hwV hw using fun t : ℝ => hVK₁ _ (hk t) (v : D₁) v.2
  let W : ℝ → V₁ := fun t => ⟨w t, hwV t⟩
  have hW : ∀ t, (((W t : V₁) : D₁) : H₁) = σ₁ (NormedSpace.exp ((t : ℂ) • X)) ((v : D₁) : H₁) := hw
  have h1 : HasDerivAt (fun t : ℝ => (((W t : V₁) : D₁) : H₁)) (((u : V₁) : D₁) : H₁) 0 := by
    have hd := hD₁.deriv X hX.1 (v : D₁)
    rw [← hu] at hd
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hW t)
  have h2 : HasDerivAt W u 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero] at h1 ⊢
    rw [← Asymptotics.isLittleO_norm_left] at h1 ⊢
    exact h1.congr_left (fun h => rfl)
  let L : V₁ →L[ℂ] H₂ := LinearMap.toContinuousLinearMap ((D₂.subtype.comp V₂.subtype).comp φ)
  have h3 : HasDerivAt (fun t => L (W t)) (L u) 0 :=
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h4 : (fun t => L (W t)) =
      fun t : ℝ => σ₂ (NormedSpace.exp ((t : ℂ) • X)) (((φ v : V₂) : D₂) : H₂) := by
    funext t
    exact hφK _ (hk t) v (W t) (hW t)
  rw [h4] at h3
  exact (hD₂.deriv X hX.1 ((φ v : V₂) : D₂)).unique h3
end ReciprocityTheory.ChartRestriction.DS.USum
