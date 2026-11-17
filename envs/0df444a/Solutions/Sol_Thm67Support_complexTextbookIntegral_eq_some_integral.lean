-- Prove2me | solution 1 for Thm67Support.complexTextbookIntegral_eq_some_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:16:20.949728+00:00
-- url     : https://prove2.me/submissions/37b3a2af-f7e5-40e0-a8d4-5e5ffa19400e

import Theorems.Thm_Thm67Support_def66Real_textbookValue_eq_integral
import Theorems.Thm_Thm67Support_def66Real_textbookIntegrable_iff
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_5_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
namespace Thm67Support
end Thm67Support
section Thm67Support
open Thm67Support

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℂ} (hZm : Measurable Z) (hZ : Integrable Z μ) :
    complexTextbookIntegral μ Z = some (∫ ω, Z ω ∂μ) := by
  rw [ complexTextbookIntegral ];
  split_ifs with hZ';
  · rw [ def66Real_textbookValue_eq_integral, def66Real_textbookValue_eq_integral ];
    · rw [ ← integral_re_add_im hZ ] ;
      norm_num [ mul_comm ];
    · exact hZ.im;
    · exact hZ.re;
  · contrapose! hZ';
    exact ⟨ def66Real_textbookIntegrable_iff ( Complex.measurable_re.comp hZm ) |>.2 hZ.re, def66Real_textbookIntegrable_iff ( Complex.measurable_im.comp hZm ) |>.2 hZ.im ⟩
end Thm67Support
