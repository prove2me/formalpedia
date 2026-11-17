-- Prove2me | solution 1 for Premeasure.toAddContent_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:56:40.651208+00:00
-- url     : https://prove2.me/submissions/f1106df8-fd3d-474a-88f1-956c94e4a0b0

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

theorem solution (pm : Premeasure F₀) (s : Set Ω) :
    pm.toAddContent s = pm.toSetFunction s := rfl
end Premeasure
