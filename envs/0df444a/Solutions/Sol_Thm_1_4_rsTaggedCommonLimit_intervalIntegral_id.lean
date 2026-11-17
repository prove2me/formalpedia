-- Prove2me | solution 1 for Thm_1_4.rsTaggedCommonLimit_intervalIntegral_id
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:45:04.38695+00:00
-- url     : https://prove2.me/submissions/c967406c-2cd8-4dde-8373-9c82863ef97d

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F001
import Theorems.Thm_Thm_1_4_rsUpperLowerCommonLimit_intervalIntegral_id
import Theorems.Thm_Thm_1_4_taggedCommonLimit_of_upperLowerCommonLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory DarbouxRS Thm_1_4
open scoped BigOperators Pointwise Interval
noncomputable section

theorem solution {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    rsTaggedCommonLimit a b g (fun x => x) (∫ x in a..b, g x) :=
  taggedCommonLimit_of_upperLowerCommonLimit
    (rsUpperLowerCommonLimit_intervalIntegral_id hab hg)
