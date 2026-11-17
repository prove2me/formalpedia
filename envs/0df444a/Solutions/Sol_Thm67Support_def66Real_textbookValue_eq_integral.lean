-- Prove2me | solution 1 for Thm67Support.def66Real_textbookValue_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:14:42.201511+00:00
-- url     : https://prove2.me/submissions/c2582e67-4496-43f3-b0ba-ae4ee0c3b3b5

import Theorems.Thm_Thm67Support_textbookIntegral_realCoe_eq_some_integral
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
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Integrable f μ) :
    Def66RealSupport.textbookValue μ (fun ω => (f ω : EReal)) = ∫ ω, f ω ∂μ := by
  have := @Thm67Support.textbookIntegral_realCoe_eq_some_integral Ω _ μ f hf;
  unfold textbookIntegral at this;
  split_ifs at this ; simp_all +decide [ Def66RealSupport.textbookValue ];
  convert congr_arg EReal.toReal this using 1
  · rfl
  · rfl
end Thm67Support
