-- Prove2me | solution 1 for Thm_1_4.taggedCommonLimit_of_upperLowerCommonLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:47:59.70341+00:00
-- url     : https://prove2.me/submissions/35d2f666-1862-4e5a-be5e-7d260cf5abfc

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
import Theorems.Thm_Thm_1_4_taggedSum_between_lower_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Thm_1_4
open Set MeasureTheory
open scoped BigOperators Pointwise Interval
noncomputable section

theorem solution {f α : ℝ → ℝ} {a b L : ℝ}
    (hUL : rsUpperLowerCommonLimit a b f α L) :
    rsTaggedCommonLimit a b f α L := by
  rcases hUL with ⟨hs, hlim⟩
  refine ⟨hs, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨δ, hδ, Hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh
  have hP := Hδ P hmesh
  have hbetween := taggedSum_between_lower_upper hs P tags htags
  have hlower_abs := abs_lt.mp hP.2
  have hupper_abs := abs_lt.mp hP.1
  refine abs_lt.mpr ⟨?_, ?_⟩
  · linarith
  · linarith
