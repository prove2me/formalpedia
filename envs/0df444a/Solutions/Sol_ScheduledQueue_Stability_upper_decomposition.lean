-- Prove2me | solution 1 for ScheduledQueue.Stability.upper_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:48:44.762826+00:00
-- url     : https://prove2.me/submissions/c18d5611-8526-44b4-b139-0e6bd85e9bab

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

open ScheduledQueue.Stability in
theorem solution {Ω : Type*} (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ)
    (U : Ω → ℝ) :
    ∀ (ω : Ω) (s : ℝ), 0 ≤ s →
      revCount h ξ U s ω ≤ beta1 h ξ U s ω + ((⌊s / h⌋₊ + 1 : ℕ) : ℕ∞) + beta2 h ξ U s ω := by
  intro ω s hs
  set k : ℕ := ⌊s / h⌋₊
  set S := {j : ℤ | revArrival h ξ U j ω ∈ Ioc 0 s}
  have hsplit : S ⊆ (Neg.neg '' {j : ℤ | 1 ≤ j ∧ revArrival h ξ U (-j) ω ∈ Ioc 0 s}) ∪
      ((Finset.Icc (0 : ℤ) k : Set ℤ) ∪
        {j : ℤ | (k : ℤ) + 1 ≤ j ∧ revArrival h ξ U j ω ∈ Ioc 0 s}) := by
    intro j hj
    rcases lt_or_ge j 0 with h0 | h0
    · left
      refine ⟨-j, ⟨by omega, by simpa [S] using hj⟩, by simp⟩
    · right
      rcases le_or_gt j k with h1 | h1
      · left; simp [h0, h1]
      · right; exact ⟨by omega, hj⟩
  calc revCount h ξ U s ω = S.encard := rfl
    _ ≤ _ := encard_le_encard hsplit
    _ ≤ _ := encard_union_le _ _
    _ ≤ beta1 h ξ U s ω + (((Finset.Icc (0 : ℤ) k : Set ℤ)).encard +
          beta2 h ξ U s ω) := by
        gcongr
        · exact (encard_image_le _ _).trans le_rfl
        · exact encard_union_le _ _
    _ = _ := by
        rw [Set.encard_coe_eq_coe_finsetCard]
        simp [add_assoc]
