-- Prove2me | solution 1 for Thm66Support.textbookIntegrable_iff_realAbsIntegral_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:27:53.433645+00:00
-- url     : https://prove2.me/submissions/f40e4c48-ab12-4147-9fe3-1c81987d569e

import Definitions.Def_ProbabilityTheory_chapter_06_thm_6_6_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
section Thm66Support
open Thm66Support
open Def66RealSupport

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EReal) :
    Thm66Support.textbookIntegrable μ X ↔ Thm66Support.realAbsIntegral μ X < ⊤ := by
  constructor
  · intro hX
    simpa [Thm66Support.textbookIntegrable, Thm66Support.realAbsIntegral] using (ENNReal.add_lt_top.mpr hX)
  · intro hAbs
    constructor
    · exact lt_of_le_of_lt (le_add_of_nonneg_right bot_le) (by simpa [Thm66Support.realAbsIntegral] using hAbs)
    · exact lt_of_le_of_lt (le_add_of_nonneg_left bot_le) (by simpa [Thm66Support.realAbsIntegral] using hAbs)
end Thm66Support
