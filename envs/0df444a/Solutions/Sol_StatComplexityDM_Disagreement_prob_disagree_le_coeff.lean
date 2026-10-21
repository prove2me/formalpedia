-- Prove2me | solution 1 for StatComplexityDM.Disagreement.prob_disagree_le_coeff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:16:43.008898+00:00
-- url     : https://prove2.me/submissions/e09801d0-506e-4986-8faf-25e4280b6202

import Mathlib
import Definitions.Def_StatComplexityDM_Disagreement_Coefficient

set_option autoImplicit false
open StatComplexityDM.Disagreement

theorem solution {κ Act : Type*} [Fintype κ] (F : Set (Act → ℝ)) (R : ℝ)
    (hF : ∀ f ∈ F, ∀ π, |f π| ≤ R) (ρw : κ → ℝ) (ρpt : κ → Act) (hρ : StatComplexityDM.LowerBound.IsDist ρw)
    (Δ₀ ε₀ : ℝ) (hΔ₀ : 0 < Δ₀) (hε₀ : 0 < ε₀) (δ ε : ℝ) (hδ : Δ₀ ≤ δ) (hε : ε₀ ≤ ε) :
    distProb ρw ρpt (disagreeEvent F δ ε ρw ρpt)
      ≤ ε ^ 2 / δ ^ 2 * disagreementCoeff F Δ₀ ε₀ ρw ρpt := by
  obtain ⟨hnn, hsum⟩ := hρ
  have hp01 : ∀ A : Act → Prop, 0 ≤ distProb ρw ρpt A ∧ distProb ρw ρpt A ≤ 1 := by
    intro A
    unfold distProb
    constructor
    · apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (hnn k) (by split_ifs <;> norm_num)
    · calc _ ≤ ∑ k, ρw k * 1 := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left (by split_ifs <;> norm_num) (hnn k)
        _ = 1 := by simp [hsum]
  have hbdd : BddAbove {x : ℝ | ∃ Δ ε : ℝ, Δ₀ ≤ Δ ∧ ε₀ ≤ ε ∧
      x = Δ ^ 2 / ε ^ 2 * distProb ρw ρpt (disagreeEvent F Δ ε ρw ρpt)} := by
    refine ⟨R ^ 2 / ε₀ ^ 2, ?_⟩
    rintro x ⟨Δ, e, hΔ, he, rfl⟩
    obtain ⟨hp0, hp1⟩ := hp01 (disagreeEvent F Δ e ρw ρpt)
    by_cases hR : Δ < R
    · have hΔpos : 0 < Δ := lt_of_lt_of_le hΔ₀ hΔ
      have hepos : 0 < e := lt_of_lt_of_le hε₀ he
      have h1 : Δ ^ 2 / e ^ 2 ≤ R ^ 2 / ε₀ ^ 2 := by
        apply div_le_div₀ (sq_nonneg R) _ (by positivity) _
        · nlinarith
        · exact pow_le_pow_left₀ hε₀.le he 2
      calc Δ ^ 2 / e ^ 2 * distProb ρw ρpt (disagreeEvent F Δ e ρw ρpt)
          ≤ Δ ^ 2 / e ^ 2 * 1 := mul_le_mul_of_nonneg_left hp1 (by positivity)
        _ ≤ R ^ 2 / ε₀ ^ 2 := by linarith
    · have hempty : distProb ρw ρpt (disagreeEvent F Δ e ρw ρpt) = 0 := by
        unfold distProb
        apply Finset.sum_eq_zero
        intro k _
        have : ¬ disagreeEvent F Δ e ρw ρpt (ρpt k) := by
          rintro ⟨f, hf, h1, _⟩
          have := hF f hf (ρpt k)
          linarith [not_lt.1 hR]
        simp [this]
      rw [hempty]
      simp only [mul_zero]
      positivity
  have hmem : δ ^ 2 / ε ^ 2 * distProb ρw ρpt (disagreeEvent F δ ε ρw ρpt) ∈
      {x : ℝ | ∃ Δ ε : ℝ, Δ₀ ≤ Δ ∧ ε₀ ≤ ε ∧
      x = Δ ^ 2 / ε ^ 2 * distProb ρw ρpt (disagreeEvent F Δ ε ρw ρpt)} := ⟨δ, ε, hδ, hε, rfl⟩
  have hle : δ ^ 2 / ε ^ 2 * distProb ρw ρpt (disagreeEvent F δ ε ρw ρpt) ≤
      disagreementCoeff F Δ₀ ε₀ ρw ρpt :=
    le_trans (le_csSup hbdd hmem) (le_max_left _ _)
  have hδpos : 0 < δ := lt_of_lt_of_le hΔ₀ hδ
  have hepos : 0 < ε := lt_of_lt_of_le hε₀ hε
  have : distProb ρw ρpt (disagreeEvent F δ ε ρw ρpt) =
      ε ^ 2 / δ ^ 2 * (δ ^ 2 / ε ^ 2 * distProb ρw ρpt (disagreeEvent F δ ε ρw ρpt)) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hle (by positivity)
