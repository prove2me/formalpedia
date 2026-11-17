-- Prove2me | solution 1 for complexTextbookIntegral_eq_none_of_not_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:33:34.023276+00:00
-- url     : https://prove2.me/submissions/1693c792-01c4-45c0-8fc6-9f7a70753ddc

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_5_F000
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
namespace Def66RealSupport
end Def66RealSupport

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) (hZ : ¬ complexTextbookIntegrable μ Z) :
    complexTextbookIntegral μ Z = none := by
  classical
  simp [complexTextbookIntegral, hZ]
