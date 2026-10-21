-- Prove2me | solution 1 for RetailerMarketplace.Entry.dPi_formula
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:37:39.451892+00:00
-- url     : https://prove2.me/submissions/a60e955e-1002-4ac2-8fed-bd14ed8f2041

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model

set_option autoImplicit false
open RetailerMarketplace.Entry

theorem rme_hD (f lam : ℝ) (hf : f ∈ Set.Ico (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 - f * (1 - lam) := by
  obtain ⟨hf0, hf1⟩ := hf
  obtain ⟨hl0, hl1⟩ := hlam
  nlinarith [mul_nonneg hf0 hl0]

theorem rme_dpi (c f lam v : ℝ) (hf : f ∈ Set.Ico (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    dPi c f lam v = (v - vT c f) * ((1 - f) * (lam - f * (1 - lam))) / (1 - f * (1 - lam)) := by
  have hD := (rme_hD f lam hf hlam).ne'
  have hE : (1 - f) ≠ 0 := by linarith [hf.2]
  unfold dPi piSBMT_M piSBT_M pbarT vT
  generalize hDd : 1 - f * (1 - lam) = D at hD ⊢
  generalize hEd : 1 - f = E at hE ⊢
  field_simp
  subst hDd
  subst hEd
  ring

theorem rme_K (f lam : ℝ) (hf : f ∈ Set.Ico (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) :
    0 < lam - f * (1 - lam) := by
  obtain ⟨hf0, hf1⟩ := hf
  obtain ⟨hl0, hl1⟩ := hlam
  rcases lt_or_eq_of_le hl0 with h | h
  · nlinarith [mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr hf1.le)]
  · subst h; nlinarith

theorem solution (c f lam : ℝ) (hc : 0 < c) (hf : f ∈ Set.Ico (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (∀ v : ℝ, dPi c f lam v = (v - vT c f) * ((1 - f) * (lam - f * (1 - lam))) / (1 - f * (1 - lam))) ∧
      (∀ v : ℝ, vT c f < v → 0 < dPi c f lam v) ∧
      StrictMono (dPi c f lam) ∧
      (∀ f₁ f₂ v : ℝ, 0 ≤ f₁ → f₁ < f₂ → f₂ < 1 → v ∈ mp c f₂ →
        dPi c f₂ lam v < dPi c f₁ lam v) := by
  have hlam0 : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hlam.1], hlam.2⟩
  have h1 : 0 < 1 - f := by linarith [hf.2]
  have hD := rme_hD f lam hf hlam0
  have hK := rme_K f lam hf hlam
  have hpos : 0 < (1 - f) * (lam - f * (1 - lam)) / (1 - f * (1 - lam)) :=
    div_pos (mul_pos h1 hK) hD
  have form : ∀ v, dPi c f lam v =
      (v - vT c f) * ((1 - f) * (lam - f * (1 - lam)) / (1 - f * (1 - lam))) := by
    intro v; rw [rme_dpi c f lam v hf hlam0]; ring
  refine ⟨fun v => rme_dpi c f lam v hf hlam0, ?_, ?_, ?_⟩
  · intro v hv
    rw [form]; exact mul_pos (by linarith) hpos
  · intro a b hab
    rw [form a, form b]
    exact mul_lt_mul_of_pos_right (by linarith) hpos
  · intro f₁ f₂ v hf₁ h12 hf₂ hv
    have hv' : c ≤ v * (1 - f₂) := hv
    have hf1' : f₁ ∈ Set.Ico (0 : ℝ) 1 := ⟨hf₁, by linarith⟩
    have hf2' : f₂ ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, hf₂⟩
    have hv0 : 0 < v := by
      by_contra hneg
      push Not at hneg
      nlinarith
    have g : ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 → dPi c g lam v =
        (v * (1 - g) - c) * ((lam - g * (1 - lam)) / (1 - g * (1 - lam))) := by
      intro g hg
      have hg1 : (1 - g) ≠ 0 := by linarith [hg.2]
      rw [rme_dpi c g lam v hg hlam0]
      unfold vT
      field_simp
    rw [g f₂ hf2', g f₁ hf1']
    have hD1 := rme_hD f₁ lam hf1' hlam0
    have hD2 := rme_hD f₂ lam hf2' hlam0
    have hK2 := rme_K f₂ lam hf2' hlam
    have hφ2 : 0 < (lam - f₂ * (1 - lam)) / (1 - f₂ * (1 - lam)) := div_pos hK2 hD2
    have hφ : (lam - f₂ * (1 - lam)) / (1 - f₂ * (1 - lam)) ≤
        (lam - f₁ * (1 - lam)) / (1 - f₁ * (1 - lam)) := by
      rw [div_le_div_iff₀ hD2 hD1]
      have : 0 ≤ (1 - lam) ^ 2 * (f₂ - f₁) := by
        apply mul_nonneg (sq_nonneg _); linarith
      nlinarith
    have hg1 : v * (1 - f₂) - c < v * (1 - f₁) - c := by nlinarith
    have hg2 : 0 ≤ v * (1 - f₂) - c := by linarith
    calc (v * (1 - f₂) - c) * ((lam - f₂ * (1 - lam)) / (1 - f₂ * (1 - lam)))
        < (v * (1 - f₁) - c) * ((lam - f₂ * (1 - lam)) / (1 - f₂ * (1 - lam))) :=
          mul_lt_mul_of_pos_right hg1 hφ2
      _ ≤ (v * (1 - f₁) - c) * ((lam - f₁ * (1 - lam)) / (1 - f₁ * (1 - lam))) :=
          mul_le_mul_of_nonneg_left hφ (by linarith)
