-- Prove2me | solution 1 for SluggishCapability.Myopic.two_state_feasible
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:31:07.761616+00:00
-- url     : https://prove2.me/submissions/3e36bfc1-05c8-49f7-af23-ea2441a7a1ff

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting

open MarkovMixing

open SluggishCapability.Myopic in
theorem solution (μ : ℕ) :
    (∀ β : ℝ, 0 < β → β ≤ 1 →
      IsStochastic (twoStateP β) ∧ MarkovMixing.Irreducible (twoStateP β) ∧
      IsStationary (twoStateP β) ![β / (1 + β), 1 / (1 + β)] ∧
      ∑ s : Fin 2, ![β / (1 + β), 1 / (1 + β)] s * (twoStateF μ s : ℝ) =
        2 * (μ : ℝ) / (1 + β)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ β₀ : ℝ, 0 ≤ β₀ ∧ β₀ < 1 ∧
      ∀ β : ℝ, β₀ < β → β < 1 → 2 * (μ : ℝ) / (1 + β) ≤ (μ : ℝ) + ε := by
  constructor
  · intro β hβ hβ1
    have h1β : (0 : ℝ) < 1 + β := by linarith
    refine ⟨⟨?_, ?_⟩, ?_, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro x y
      fin_cases x <;> fin_cases y <;> simp [twoStateP] <;> linarith
    · intro x
      fin_cases x <;> simp [twoStateP, Fin.sum_univ_two]
    · intro x y
      fin_cases x <;> fin_cases y
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp [twoStateP]⟩
      · exact ⟨1, by simp [twoStateP, hβ]⟩
      · exact ⟨0, by simp⟩
    · intro x
      fin_cases x <;> simp <;> positivity
    · simp [Fin.sum_univ_two]
      field_simp
      ring
    · funext x
      fin_cases x <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, twoStateP] <;>
        field_simp <;> ring
    · simp [Fin.sum_univ_two, twoStateF]
      field_simp
  · intro ε hε
    have hμ : (0 : ℝ) ≤ μ := Nat.cast_nonneg μ
    refine ⟨max 0 (((μ : ℝ) - ε) / ((μ : ℝ) + ε)), le_max_left _ _, ?_, ?_⟩
    · apply max_lt (by norm_num)
      rw [div_lt_one (by linarith)]
      linarith
    · intro β hβ hβ1
      have hβ0 : 0 < β := lt_of_le_of_lt (le_max_left _ _) hβ
      have hβ2 : ((μ : ℝ) - ε) / ((μ : ℝ) + ε) < β := lt_of_le_of_lt (le_max_right _ _) hβ
      rw [div_lt_iff₀ (by linarith)] at hβ2
      rw [div_le_iff₀ (by linarith)]
      nlinarith
