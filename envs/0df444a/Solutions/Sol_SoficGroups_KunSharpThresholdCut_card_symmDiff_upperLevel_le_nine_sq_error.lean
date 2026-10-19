-- Prove2me | solution 1 for SoficGroups.KunSharpThresholdCut.card_symmDiff_upperLevel_le_nine_sq_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/ca572ffd-03a6-4739-8673-4f0760ec9d1c

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunSharpThresholdCut
open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff
namespace SoficGroups.KunSharpThresholdCut
theorem _root_.solution {V : Type*}
    [Fintype V] [DecidableEq V]
    (T : Finset V) (f : V → ℝ) (t : ℝ)
    (hlow : (1 / 3 : ℝ) ≤ t) (hhigh : t ≤ (2 / 3 : ℝ)) :
    (((upperLevel f t ∆ T).card : ℝ)) ≤
      9 * ∑ x : V, (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2 := by
  classical
  let D : Finset V := upperLevel f t ∆ T
  have hpoint (x : V) (hx : x ∈ D) :
      (1 : ℝ) ≤
        9 * (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2 := by
    rcases (Finset.mem_symmDiff.mp hx) with hx | hx
    · obtain ⟨hxlevel, hxT⟩ := hx
      have hfx : t < f x := (Finset.mem_filter.mp hxlevel).2
      simp only [if_neg hxT]
      nlinarith [sq_nonneg (3 * f x - 1)]
    · obtain ⟨hxT, hxlevel⟩ := hx
      have hfx : f x ≤ t := by
        apply le_of_not_gt
        intro h
        exact hxlevel
          (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)
      simp only [if_pos hxT]
      nlinarith [sq_nonneg (3 * f x - 2)]
  have hcard :
      (D.card : ℝ) = ∑ x : V, if x ∈ D then (1 : ℝ) else 0 := by
    simp
  change (D.card : ℝ) ≤ _
  rw [hcard]
  calc
    (∑ x : V, if x ∈ D then (1 : ℝ) else 0) ≤
        ∑ x : V,
          9 * (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x ∈ D
      · simpa only [if_pos hx] using hpoint x hx
      · simp only [if_neg hx]
        positivity
    _ = 9 * ∑ x : V,
        (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2 := by
      rw [Finset.mul_sum]
end SoficGroups.KunSharpThresholdCut
