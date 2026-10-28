-- Prove2me | solution 2 for OnlineLearningOCO.Winnow.theorem_3_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:46.409626+00:00
-- url     : https://prove2.me/submissions/64ce01f3-1211-40a4-a57f-d53ccd9b4506

import Mathlib
import Definitions.Def_OnlineLearningOCO_Winnow_Winnow
import Theorems.Thm_OnlineLearningOCO_Winnow_eq_3_3
import Theorems.Thm_OnlineLearningOCO_Winnow_eq_3_4

-- carved verbatim out of submission c93de0a4-8301-41f9-b2db-8cddf3f26c85, lines 227-254

section
set_option autoImplicit false
open Finset
open OnlineLearningOCO.Winnow

theorem OLW_surr_nonneg (d : ℕ) (η : ℝ) (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ) (t : ℕ) (v : Fin d → ℝ) :
    0 ≤ winnowSurrogate d η x y t v := by
  unfold winnowSurrogate
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem OLW_310ab (d k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2)
    (x : ℕ → Fin d → ℝ) (hx : ∀ t i, x t i = 0 ∨ x t i = 1)
    (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1)
    (u : Fin d → ℝ) (hu : ∀ i, u i = 0 ∨ u i = 1) (hu1 : ∑ i, u i = (k : ℝ)) (T : ℕ) :
    ((winnowMistakes d η x y T).card : ℝ) ≤
        ∑ t ∈ range T, winnowSurrogate d η x y t (winnowWeights d η x y t) ∧
    ∑ t ∈ range T, winnowSurrogate d η x y t (winnowWeights d η x y t) ≤
        (1 / (1 - 2 * η)) *
          (∑ t ∈ range T, winnowSurrogate d η x y t u + (k : ℝ) * Real.log d / η) := by
  constructor
  · unfold winnowMistakes
    rw [card_filter]
    push_cast
    apply sum_le_sum
    intro t _
    by_cases hm : winnowMargin d η x y t ≤ 0
    · have hm' : y t * (2 * ∑ i, winnowWeights d η x y t i * x t i - 1) ≤ 0 := hm
      simp only [hm, if_true, winnowSurrogate]
      refine le_trans ?_ (le_max_right _ _)
      linarith
    · simp only [hm, if_false]
      exact OLW_surr_nonneg d η x y t _
  · obtain ⟨_, h2⟩ := OnlineLearningOCO.Winnow.eq_3_3 d k hk η hη hη2.le x hx y hy u hu hu1 T
    obtain ⟨h1, _⟩ := OnlineLearningOCO.Winnow.eq_3_3 d k hk η hη hη2.le x hx y hy u hu hu1 T
    have h34 : ∑ t ∈ range T, ∑ i, winnowWeights d η x y t i * winnowZ d η x y t i ^ 2 ≤
        2 * ∑ t ∈ range T, winnowSurrogate d η x y t (winnowWeights d η x y t) := by
      rw [mul_sum]
      exact sum_le_sum (fun t _ => OnlineLearningOCO.Winnow.eq_3_4 d η x hx y hy t)
    rw [sum_sub_distrib] at h1
    have hpos : 0 < 1 - 2 * η := by linarith
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hpos]
    have := mul_le_mul_of_nonneg_left h34 hη.le
    have e : (k : ℝ) * Real.log d / η * 1 = (k : ℝ) * Real.log d / η := mul_one _
    nlinarith

theorem solution (d k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2)
    (x : ℕ → Fin d → ℝ) (hx : ∀ t i, x t i = 0 ∨ x t i = 1)
    (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1)
    (u : Fin d → ℝ) (hu : ∀ i, u i = 0 ∨ u i = 1) (hu1 : ∑ i, u i = (k : ℝ)) (T : ℕ) :
    ((winnowMistakes d η x y T).card : ℝ) ≤
        ∑ t ∈ range T, winnowSurrogate d η x y t (winnowWeights d η x y t) ∧
    ∑ t ∈ range T, winnowSurrogate d η x y t (winnowWeights d η x y t) ≤
        (1 / (1 - 2 * η)) *
          (∑ t ∈ range T, winnowSurrogate d η x y t u + (k : ℝ) * Real.log d / η) ∧
    ((∀ t < T, 1 ≤ y t * (2 * ∑ i, u i * x t i - 1)) →
      ((winnowMistakes d (1 / 4) x y T).card : ℝ) ≤ 8 * (k : ℝ) * Real.log d) := by
  obtain ⟨h1, h2⟩ := OLW_310ab d k hk η hη hη2 x hx y hy u hu hu1 T
  refine ⟨h1, h2, ?_⟩
  intro hmar
  obtain ⟨a1, a2⟩ := OLW_310ab d k hk (1 / 4) (by norm_num) (by norm_num) x hx y hy u hu hu1 T
  have hG : ∑ t ∈ range T, winnowSurrogate d (1 / 4) x y t u = 0 := by
    apply sum_eq_zero
    intro t ht
    have := hmar t (mem_range.1 ht)
    unfold winnowSurrogate
    split_ifs
    · apply max_eq_left; linarith
    · rfl
  rw [hG] at a2
  have : (1 / (1 - 2 * (1 / 4 : ℝ))) * (0 + (k : ℝ) * Real.log d / (1 / 4)) = 8 * (k : ℝ) * Real.log d := by
    ring
  linarith

end
