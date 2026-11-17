-- Prove2me | solution 1 for Thm_1_4.rsUpperLowerCommonLimit_intervalIntegral_id
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:43:44.968829+00:00
-- url     : https://prove2.me/submissions/b7f62d76-7b61-4637-910e-92be0407cc9d

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Theorems.Thm_Thm_1_4_partition_integral_between_lower_upper_id
import Theorems.Thm_Thm_1_4_upper_lower_gap_small_continuous_id
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory DarbouxRS Thm_1_4
open scoped BigOperators Pointwise Interval
noncomputable section

private theorem source_rsUpperLowerCommonLimit_intervalIntegral_id {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    rsUpperLowerCommonLimit a b g (fun x => x) (∫ x in a..b, g x) := by
  have hAbove : BddAbove (g '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddAbove
  have hBelow : BddBelow (g '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddBelow
  refine ⟨⟨hab, hAbove, hBelow, monotoneOn_id⟩, ?_⟩
  intro eps heps
  rcases upper_lower_gap_small_continuous_id hab hg eps heps with
    ⟨δ, hδ_pos, Hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro P hmesh
  have hbetween := partition_integral_between_lower_upper_id hg P
  have hgap := Hδ P hmesh
  constructor
  · refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith
  · refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith

theorem solution {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    rsUpperLowerCommonLimit a b g (fun x => x) (∫ x in a..b, g x) := by
  exact source_rsUpperLowerCommonLimit_intervalIntegral_id hab hg
