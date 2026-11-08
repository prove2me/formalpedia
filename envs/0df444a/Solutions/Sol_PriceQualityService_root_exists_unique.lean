-- Prove2me | solution 1 for PriceQualityService.root_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:01:55.229473+00:00
-- url     : https://prove2.me/submissions/444977d3-3874-491c-8956-f1a90cc2f093

import Mathlib

theorem solution {N : ℕ} (w : Fin N → ℝ) :
    ∃! r : ℝ, r = ∑ i, Real.exp (w i - r - 1) := by
  have anti : ∀ a b : ℝ, a ≤ b → ∑ i, Real.exp (w i - b - 1) ≤ ∑ i, Real.exp (w i - a - 1) :=
    fun a b hab => Finset.sum_le_sum (fun i _ => Real.exp_le_exp.mpr (by linarith))
  have hS0 : 0 ≤ ∑ i, Real.exp (w i - 0 - 1) :=
    Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
  have hcont : Continuous (fun r : ℝ => r - ∑ i, Real.exp (w i - r - 1)) := by fun_prop
  have hmem : (0:ℝ) ∈ Set.Icc ((fun r : ℝ => r - ∑ i, Real.exp (w i - r - 1)) 0)
      ((fun r : ℝ => r - ∑ i, Real.exp (w i - r - 1)) (∑ i, Real.exp (w i - 0 - 1))) := by
    constructor
    · show 0 - ∑ i, Real.exp (w i - 0 - 1) ≤ 0
      linarith
    · show 0 ≤ (∑ i, Real.exp (w i - 0 - 1)) -
        ∑ i, Real.exp (w i - (∑ i, Real.exp (w i - 0 - 1)) - 1)
      linarith [anti 0 _ hS0]
  obtain ⟨r, -, hr⟩ := intermediate_value_Icc hS0 hcont.continuousOn hmem
  have hr' : r - ∑ i, Real.exp (w i - r - 1) = 0 := hr
  refine ⟨r, by linarith, ?_⟩
  intro y hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := anti y r h.le
    linarith
  · have := anti r y h.le
    linarith
