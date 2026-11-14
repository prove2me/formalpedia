-- Prove2me | solution 1 for avram_chat24_uniform_left_cell_limit_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:06:38.396391+00:00
-- url     : https://prove2.me/submissions/d220f2b5-2d25-4d2d-9898-26b8b2f14c9f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_chat24_strict_mono_cell_selector
import Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_cell_approach_left
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution (B : ℝ≥0) (hB : 0 < B)
    (t : ℝ≥0) (ht : 0 < t) (htB : t ≤ B) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    ∃ k : ℕ → ℕ,
      (∀ n, k n < n + 1 ∧ u n (k n) < t ∧ t ≤ u n (k n + 1)) ∧
      (∀ n j, u n j < t → t ≤ u n (j + 1) → j = k n) ∧
      Tendsto (fun n => u n (k n)) atTop (𝓝[<] t) := by
  let u (n i : ℕ) : ℝ≥0 := B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
  change ∃ k : ℕ → ℕ, (∀ n, k n < n + 1 ∧ u n (k n) < t ∧ t ≤ u n (k n + 1)) ∧
    (∀ n j, u n j < t → t ≤ u n (j + 1) → j = k n) ∧
    Tendsto (fun n => u n (k n)) atTop (𝓝[<] t)
  have hu (n : ℕ) : StrictMono (u n) := by
    intro i j hij
    dsimp [u]
    apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ≥0) < ((n + 1 : ℕ) : ℝ≥0))).2
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) hB
  have hend (n : ℕ) : u n (n + 1) = B := by
    have hd : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := ne_of_gt (by positivity)
    simp [u, hd]
  have hs (n : ℕ) := AvramDividend.Classical.avram_chat24_strict_mono_cell_selector
    (u n) (hu n) (n + 1) t (by simpa [u] using ht) (by simpa only [hend] using htB)
  choose k hk hleft hright huniq using hs
  refine ⟨k, fun n => ⟨hk n, hleft n, hright n⟩, huniq, ?_⟩
  exact AvramDividend.Classical.avram_chat24_uniform_cell_approach_left B t k
    (fun n => ⟨hleft n, hright n⟩)
