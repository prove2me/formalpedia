-- Prove2me | solution 1 for SensitivityPoA.SmallDemand.poa_demandNormalize
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:11:42.685205+00:00
-- url     : https://prove2.me/submissions/59b792b9-28fb-49f2-aae5-8d5bf3f650f1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_SmallDemand_Setting

set_option autoImplicit false

open SensitivityPoA.SmallDemand KellyStochasticNetworks
open scoped Pointwise

section mmD
variable {N : Network}

lemma mmD_link (υ : ℝ) (f : Fin N.R → ℝ) (j : Fin N.J) :
    linkFlow N.A (fun r => f r / υ) j = linkFlow N.A f j / υ := by
  unfold linkFlow
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun r _ => by ring

lemma mmD_tau (υ : ℝ) (hυ : 0 < υ) (Γ : Game N) (f : Fin N.R → ℝ) (j : Fin N.J) :
    (demandNormalize υ Γ).τ j (linkFlow N.A (fun r => f r / υ) j) = Γ.τ j (linkFlow N.A f j) := by
  rw [mmD_link]
  show Γ.τ j (linkFlow N.A f j / υ * υ) = _
  rw [div_mul_cancel₀ _ hυ.ne']

lemma mmD_flow (υ : ℝ) (hυ : 0 < υ) (Γ : Game N) (f : Fin N.R → ℝ) :
    IsFlow (demandNormalize υ Γ) (fun r => f r / υ) ↔ IsFlow Γ f := by
  unfold IsFlow wardropFeasible
  show ((∀ r, 0 ≤ f r / υ) ∧ ∀ σ, (∑ r ∈ Finset.univ.filter (fun r => N.s r = σ), f r / υ) = Γ.d σ / υ) ↔
    ((∀ r, 0 ≤ f r) ∧ ∀ σ, (∑ r ∈ Finset.univ.filter (fun r => N.s r = σ), f r) = Γ.d σ)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun r => ?_, fun σ => ?_⟩
    · have := mul_nonneg (h1 r) hυ.le
      rwa [div_mul_cancel₀ _ hυ.ne'] at this
    · have := h2 σ
      rw [← Finset.sum_div] at this
      exact (div_left_inj' hυ.ne').mp this
  · rintro ⟨h1, h2⟩
    exact ⟨fun r => div_nonneg (h1 r) hυ.le, fun σ => by rw [← Finset.sum_div, h2 σ]⟩

lemma mmD_cost (υ : ℝ) (hυ : 0 < υ) (Γ : Game N) (f : Fin N.R → ℝ) :
    cost Γ f = υ * cost (demandNormalize υ Γ) (fun r => f r / υ) := by
  unfold cost
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mmD_tau υ hυ, mmD_link]
  field_simp

lemma mmD_path (υ : ℝ) (hυ : 0 < υ) (Γ : Game N) (f : Fin N.R → ℝ) (r : Fin N.R) :
    pathCost (demandNormalize υ Γ) (fun r => f r / υ) r = pathCost Γ f r := by
  unfold pathCost
  exact Finset.sum_congr rfl fun j _ => by rw [mmD_tau υ hυ]

lemma mmD_WE (υ : ℝ) (hυ : 0 < υ) (Γ : Game N) (f : Fin N.R → ℝ) :
    IsWE (demandNormalize υ Γ) (fun r => f r / υ) ↔ IsWE Γ f := by
  unfold IsWE IsWardropEquilibrium
  have hF := mmD_flow υ hυ Γ f
  have key : ∀ r r' : Fin N.R,
      (∑ j, (demandNormalize υ Γ).τ j (linkFlow N.A (fun r => f r / υ) j) * N.A j r) =
        ∑ j, Γ.τ j (linkFlow N.A f j) * N.A j r := fun r r' =>
    Finset.sum_congr rfl fun j _ => by rw [mmD_tau υ hυ]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hF.mp h1, fun r r' hs hr => ?_⟩
    have := h2 r r' hs (div_pos hr hυ)
    rwa [key r r', key r' r] at this
  · rintro ⟨h1, h2⟩
    refine ⟨hF.mpr h1, fun r r' hs hr => ?_⟩
    have := h2 r r' hs (by
      have := mul_pos hr hυ
      rwa [div_mul_cancel₀ _ hυ.ne'] at this)
    rwa [key r r', key r' r]

lemma mmD_SO (υ : ℝ) (hυ : 0 < υ) (Γ : Game N) (f : Fin N.R → ℝ) :
    IsSO (demandNormalize υ Γ) (fun r => f r / υ) ↔ IsSO Γ f := by
  unfold IsSO
  rw [mmD_flow υ hυ]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h g hg
    have := h (fun r => g r / υ) ((mmD_flow υ hυ Γ g).mpr hg)
    rw [mmD_cost υ hυ Γ f, mmD_cost υ hυ Γ g]
    exact mul_le_mul_of_nonneg_left this hυ.le
  · intro h g' hg'
    have hg : IsFlow Γ (fun r => g' r * υ) := by
      rw [← mmD_flow υ hυ]
      have : (fun r => g' r * υ / υ) = g' := by
        funext r; field_simp
      rw [this]; exact hg'
    have := h _ hg
    rw [mmD_cost υ hυ Γ f, mmD_cost υ hυ Γ (fun r => g' r * υ)] at this
    have e : (fun r => g' r * υ / υ) = g' := by funext r; field_simp
    rw [e] at this
    exact le_of_mul_le_mul_left this hυ

lemma mmD_WEcost (υ : ℝ) (hυ : 0 < υ) (Γ : Game N) :
    WECost (demandNormalize υ Γ) = WECost Γ / υ := by
  unfold WECost
  have : cost (demandNormalize υ Γ) '' {f | IsWE (demandNormalize υ Γ) f} =
      υ⁻¹ • (cost Γ '' {f | IsWE Γ f}) := by
    ext c
    constructor
    · rintro ⟨f', hf', rfl⟩
      refine ⟨cost Γ (fun r => f' r * υ), ⟨_, ?_, rfl⟩, ?_⟩
      · show IsWE Γ _
        have e : (fun r => f' r * υ / υ) = f' := by funext r; field_simp
        rw [← mmD_WE υ hυ, e]; exact hf'
      · have e : (fun r => f' r * υ / υ) = f' := by funext r; field_simp
        rw [mmD_cost υ hυ Γ (fun r => f' r * υ), e]
        simp only [smul_eq_mul]
        field_simp
    · rintro ⟨c0, ⟨f, hf, rfl⟩, rfl⟩
      refine ⟨fun r => f r / υ, (mmD_WE υ hυ Γ f).mpr hf, ?_⟩
      rw [mmD_cost υ hυ Γ f]
      simp only [smul_eq_mul]
      field_simp
  rw [this, Real.sSup_smul_of_nonneg (inv_nonneg.mpr hυ.le)]
  simp [div_eq_inv_mul]

lemma mmD_SOcost (υ : ℝ) (hυ : 0 < υ) (Γ : Game N) :
    SOCost (demandNormalize υ Γ) = SOCost Γ / υ := by
  unfold SOCost
  have : cost (demandNormalize υ Γ) '' {f | IsFlow (demandNormalize υ Γ) f} =
      υ⁻¹ • (cost Γ '' {f | IsFlow Γ f}) := by
    ext c
    constructor
    · rintro ⟨f', hf', rfl⟩
      have e : (fun r => f' r * υ / υ) = f' := by funext r; field_simp
      refine ⟨cost Γ (fun r => f' r * υ), ⟨_, ?_, rfl⟩, ?_⟩
      · show IsFlow Γ _
        rw [← mmD_flow υ hυ, e]; exact hf'
      · rw [mmD_cost υ hυ Γ (fun r => f' r * υ), e]
        simp only [smul_eq_mul]
        field_simp
    · rintro ⟨c0, ⟨f, hf, rfl⟩, rfl⟩
      refine ⟨fun r => f r / υ, (mmD_flow υ hυ Γ f).mpr hf, ?_⟩
      rw [mmD_cost υ hυ Γ f]
      simp only [smul_eq_mul]
      field_simp
  rw [this, Real.sInf_smul_of_nonneg (inv_nonneg.mpr hυ.le)]
  simp [div_eq_inv_mul]

end mmD

theorem solution {N : Network} (Γ : Game N) (hΓ : Γ ∈ gameSpace N) (υ : ℝ)
    (hυ : 0 < υ) :
    demandNormalize υ Γ ∈ gameSpace N ∧
    (∀ f : Fin N.R → ℝ, IsWE Γ f ↔ IsWE (demandNormalize υ Γ) (fun r => f r / υ)) ∧
    (∀ f : Fin N.R → ℝ, IsSO Γ f ↔ IsSO (demandNormalize υ Γ) (fun r => f r / υ)) ∧
    (∀ f : Fin N.R → ℝ, IsFlow Γ f →
      cost Γ f = υ * cost (demandNormalize υ Γ) (fun r => f r / υ)) ∧
    PoA (demandNormalize υ Γ) = PoA Γ := by
  refine ⟨?_, fun f => (mmD_WE υ hυ Γ f).symm, fun f => (mmD_SO υ hυ Γ f).symm,
    fun f _ => mmD_cost υ hυ Γ f, ?_⟩
  · obtain ⟨⟨hc, hd⟩, hT, hp⟩ := hΓ
    refine ⟨⟨fun j => ?_, fun k => div_nonneg (hd k) hυ.le⟩, ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hc j
      have hm : Set.MapsTo (fun x : ℝ => x * υ) (Set.Ici 0) (Set.Ici 0) :=
        fun x hx => mul_nonneg hx hυ.le
      refine ⟨?_, ?_, fun x hx => h3 _ (mul_nonneg hx hυ.le)⟩
      · exact h1.comp (continuous_id.mul continuous_const).continuousOn hm
      · intro x hx y hy hxy
        exact h2 (mul_nonneg hx hυ.le) (mul_nonneg hy hυ.le) (mul_le_mul_of_nonneg_right hxy hυ.le)
    · unfold totalDemand at hT ⊢
      show 0 < ∑ k, Γ.d k / υ
      rw [← Finset.sum_div]
      exact div_pos hT hυ
    · intro j x hx hxT
      have hT' : totalDemand (demandNormalize υ Γ).d = totalDemand Γ.d / υ := by
        unfold totalDemand
        show ∑ k, Γ.d k / υ = _
        rw [Finset.sum_div]
      rw [hT'] at hxT
      show 0 < Γ.τ j (x * υ)
      apply hp j _ (mul_pos hx hυ)
      rw [le_div_iff₀ hυ] at hxT
      exact hxT
  · unfold PoA
    rw [mmD_WEcost υ hυ Γ, mmD_SOcost υ hυ Γ, div_div_div_cancel_right₀ hυ.ne']
