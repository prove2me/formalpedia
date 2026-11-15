-- Prove2me | solution 1 for Real.exists_unique_zero_of_le_deriv_of_abs_lt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T20:37:07.245977+00:00
-- url     : https://prove2.me/submissions/2d24edcd-9c63-4ec5-b504-0616807496d0

import Mathlib

open Filter Topology

namespace RH9

/-- One-dimensional root in a window: `f' ≥ c > 0` on `[-η, η]` and `|f 0| < c η`. -/
lemma ktr_root_1d {f : ℝ → ℝ} (hf : Differentiable ℝ f) {η c : ℝ} (hη : 0 < η) (hc : 0 < c)
    (hd : ∀ σ, |σ| ≤ η → c ≤ deriv f σ) (h0 : |f 0| < c * η) :
    ∃ σ, |σ| < η ∧ f σ = 0 ∧ ∀ σ', |σ'| < η → f σ' = 0 → σ' = σ := by
  have hD : Convex ℝ (Set.Icc (-η) η) := convex_Icc _ _
  have hge : ∀ x ∈ interior (Set.Icc (-η) η), c ≤ deriv f x := by
    rw [interior_Icc]; intro x hx; exact hd x (abs_le.2 ⟨hx.1.le, hx.2.le⟩)
  have hmvt := hD.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn
    hf.differentiableOn hge
  have hmem : ∀ σ, |σ| ≤ η → σ ∈ Set.Icc (-η) η := fun σ h => abs_le.1 h
  have h0m : (0 : ℝ) ∈ Set.Icc (-η) η := hmem 0 (by simp [hη.le])
  have hηm : η ∈ Set.Icc (-η) η := hmem η (by rw [abs_of_pos hη])
  have hηm' : -η ∈ Set.Icc (-η) η := hmem (-η) (by rw [abs_neg, abs_of_pos hη])
  have h1 := hmvt 0 h0m η hηm hη.le
  have h2 := hmvt (-η) hηm' 0 h0m (by linarith)
  have h0' := abs_lt.1 h0
  have hpos : 0 < f η := by nlinarith
  have hneg : f (-η) < 0 := by nlinarith
  obtain ⟨σ, hσ, hfσ⟩ := intermediate_value_Ioo (by linarith : -η ≤ η)
    hf.continuous.continuousOn ⟨hneg, hpos⟩
  have hσa : |σ| < η := abs_lt.2 ⟨hσ.1, hσ.2⟩
  refine ⟨σ, hσa, hfσ, fun σ' hσ' hf' => ?_⟩
  have hσ'm := hmem σ' hσ'.le
  have hσm := hmem σ hσa.le
  rcases lt_trichotomy σ' σ with h | h | h
  · have := hmvt σ' hσ'm σ hσm h.le
    rw [hfσ, hf'] at this; nlinarith
  · exact h
  · have := hmvt σ hσm σ' hσ'm h.le
    rw [hfσ, hf'] at this; nlinarith

end RH9

open Real

theorem solution {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {η c : ℝ} (hη : 0 < η) (hc : 0 < c)
    (hd : ∀ σ, |σ| ≤ η → c ≤ deriv f σ) (h0 : |f 0| < c * η) :
    ∃ σ, |σ| < η ∧ f σ = 0 ∧ ∀ σ', |σ'| < η → f σ' = 0 → σ' = σ :=
  RH9.ktr_root_1d hf hη hc hd h0
