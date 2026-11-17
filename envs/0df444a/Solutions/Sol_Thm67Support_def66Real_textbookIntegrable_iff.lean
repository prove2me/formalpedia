-- Prove2me | solution 1 for Thm67Support.def66Real_textbookIntegrable_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:09:04.144045+00:00
-- url     : https://prove2.me/submissions/a300ae59-72b6-405e-9317-881493fbb283

import Theorems.Thm_Thm67Support_realCoe_textbookIntegrable_iff
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

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfm : Measurable f) :
    Def66RealSupport.textbookIntegrable μ (fun ω => (f ω : EReal)) ↔ Integrable f μ := by
  convert realCoe_textbookIntegrable_iff hfm using 1
  rfl
end Thm67Support
