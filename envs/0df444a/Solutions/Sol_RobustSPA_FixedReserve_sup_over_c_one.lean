-- Prove2me | solution 1 for RobustSPA.FixedReserve.sup_over_c_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:51:42.878556+00:00
-- url     : https://prove2.me/submissions/194b075b-73e3-4e57-8acb-0a6317697d62

import Mathlib
import Definitions.Def_RobustSPA_FixedReserve_Setting

open MeasureTheory
open RobustSPA.FixedReserve

theorem solution(r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    IsGreatest ((fun c : ℝ => r * c + (1 - r) * (1 - c)) '' Set.Icc 0 1) (max (1 - r) r) := by
  obtain ⟨h0, h1⟩ := hr
  refine ⟨?_, ?_⟩
  · rcases le_total r (1 - r) with h | h
    · exact ⟨0, ⟨le_refl _, zero_le_one⟩, by rw [max_eq_left h]; ring⟩
    · exact ⟨1, ⟨zero_le_one, le_refl _⟩, by rw [max_eq_right h]; ring⟩
  · rintro _ ⟨c, ⟨hc0, hc1⟩, rfl⟩
    rcases le_total r (1 - r) with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith
