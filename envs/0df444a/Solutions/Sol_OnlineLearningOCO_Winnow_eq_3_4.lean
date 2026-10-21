-- Prove2me | solution 1 for OnlineLearningOCO.Winnow.eq_3_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:05:21.451689+00:00
-- url     : https://prove2.me/submissions/f11a31a7-97ad-4a2d-a3b6-652790f44280

import Mathlib
import Definitions.Def_OnlineLearningOCO_Winnow_Winnow
set_option autoImplicit false
open Finset
open OnlineLearningOCO.Winnow

theorem OLW_34 (d : ℕ) (η : ℝ) (x : ℕ → Fin d → ℝ) (hx : ∀ t i, x t i = 0 ∨ x t i = 1)
    (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1) (t : ℕ) :
    ∑ i, winnowWeights d η x y t i * winnowZ d η x y t i ^ 2 ≤
      2 * winnowSurrogate d η x y t (winnowWeights d η x y t) := by
  by_cases hm : winnowMargin d η x y t ≤ 0
  · have hm' : y t * (2 * ∑ i, winnowWeights d η x y t i * x t i - 1) ≤ 0 := hm
    have hz : ∀ i, winnowWeights d η x y t i * winnowZ d η x y t i ^ 2 =
        4 * (winnowWeights d η x y t i * x t i) := by
      intro i
      simp only [winnowZ, hm, if_true]
      rcases hx t i with h | h <;> rcases hy t with h' | h' <;> rw [h, h'] <;> ring
    simp only [winnowSurrogate, hm, if_true]
    rw [sum_congr rfl (fun i _ => hz i), ← mul_sum]
    set p := ∑ i, winnowWeights d η x y t i * x t i
    have hmax : max 0 (1 - y t * (2 * p - 1)) = 1 - y t * (2 * p - 1) := by
      apply max_eq_right
      linarith
    rw [hmax]
    rcases hy t with h' | h' <;> rw [h'] at hm' ⊢ <;> linarith
  · simp [winnowSurrogate, winnowZ, hm]


theorem solution (d : ℕ) (η : ℝ) (x : ℕ → Fin d → ℝ) (hx : ∀ t i, x t i = 0 ∨ x t i = 1)
    (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1) (t : ℕ) :
    ∑ i, winnowWeights d η x y t i * winnowZ d η x y t i ^ 2 ≤
      2 * winnowSurrogate d η x y t (winnowWeights d η x y t) :=
  OLW_34 d η x hx y hy t
