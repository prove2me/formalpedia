-- Prove2me | solution 1 for Premeasure.toAddContent_isSigmaSubadditive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:56:47.543205+00:00
-- url     : https://prove2.me/submissions/17a4262d-05b5-467a-a83b-c576cd9dd911

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F001
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F000
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set ENNReal Function MeasureTheory
section Premeasure
open Premeasure
variable {Ω : Type*} {F₀ : FieldOfSets Ω}

theorem solution (pm : Premeasure F₀) :
    pm.toAddContent.IsSigmaSubadditive := by
  apply isSigmaSubadditive_of_addContent_iUnion_eq_tsum F₀.isSetRing
  intro f hf hU hdisj
  change pm.toSetFunction (⋃ i, f i) = ∑' i, pm.toSetFunction (f i)
  rw [pm.toSetFunction_of_mem hU]
  simp_rw [pm.toSetFunction_of_mem (hf _)]
  exact pm.sigma_additive f hf hU hdisj
end Premeasure
