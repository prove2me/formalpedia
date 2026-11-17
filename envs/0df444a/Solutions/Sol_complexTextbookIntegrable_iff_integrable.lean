-- Prove2me | solution 1 for complexTextbookIntegrable_iff_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:18:40.044166+00:00
-- url     : https://prove2.me/submissions/982d91b7-b7c0-463d-aa32-7b42a75c744c

import Theorems.Thm_Thm67Support_def66Real_textbookIntegrable_iff
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

/-- Original source forward implication isolated for the published proof. -/
private theorem source_complex_to_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℂ} (hZm : Measurable Z)
    (hZ_integrable : complexTextbookIntegrable μ Z) :
    Integrable Z μ := by
  obtain ⟨hZ_re, hZ_im⟩ := hZ_integrable
  have hZ_re_integrable : Integrable (fun ω => (Z ω).re) μ := by
    convert Thm67Support.def66Real_textbookIntegrable_iff _ |>.1 hZ_re using 1;
    exact Complex.measurable_re.comp hZm
  have hZ_im_integrable : Integrable (fun ω => (Z ω).im) μ := by
    exact Thm67Support.def66Real_textbookIntegrable_iff ( Complex.measurable_im.comp hZm ) |>.1 hZ_im;
  convert hZ_re_integrable.ofReal.add ( hZ_im_integrable.ofReal.smul_const Complex.I ) using 1 ;
  rfl
  ext; simp  [Complex.ext_iff]
  any_goals exact ℝ
  all_goals first | infer_instance | simp +decide

/-- Original source reverse implication isolated for the published proof. -/
private theorem source_integrable_to_complex {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℂ} (hZm : Measurable Z)
    (h : Integrable Z μ) :
    complexTextbookIntegrable μ Z := by
  constructor
  · convert Thm67Support.def66Real_textbookIntegrable_iff ( Complex.measurable_re.comp hZm ) |>.2 ( h.re ) using 1;
    rfl
  · convert Thm67Support.def66Real_textbookIntegrable_iff ( show Measurable fun ω => ( Z ω |> Complex.im ) from Complex.measurable_im.comp hZm ) |>.2 ( h.im ) using 1

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℂ} (hZm : Measurable Z) :
    complexTextbookIntegrable μ Z ↔ Integrable Z μ := by
  exact ⟨source_complex_to_integrable hZm, source_integrable_to_complex hZm⟩
