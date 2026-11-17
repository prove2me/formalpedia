-- Prove2me | solution 1 for Thm67Support.realCoe_textbookIntegrable_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:07:17.495956+00:00
-- url     : https://prove2.me/submissions/90dd1cb5-052b-4099-833f-03bc99910a3a

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

/-- Source forward proof: textbook extended-real integrability implies Bochner integrability. -/
private theorem source_realCoe_to_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfm : Measurable f)
    (h_integrable : textbookIntegrable μ (fun ω => (f ω : EReal))) : Integrable f μ := by
  unfold textbookIntegrable at h_integrable
  have h_integrable_pos : MeasureTheory.Integrable (fun ω => max (f ω) 0) μ := by
    refine' ⟨ hfm.aemeasurable.max aemeasurable_const |> fun h => h.aestronglyMeasurable, _ ⟩;
    convert h_integrable.1 using 1;
    simp +decide [ hasFiniteIntegral_iff_norm, Def65Support.posLIntegral ];
    simp +decide [Def65Support.posPart, abs_of_nonneg]
  have h_integrable_neg : MeasureTheory.Integrable (fun ω => max (-f ω) 0) μ := by
    refine' ⟨ _, _ ⟩;
    · exact Measurable.aestronglyMeasurable ( by measurability );
    · convert h_integrable.2 using 1;
      simp +decide [ hasFiniteIntegral_iff_norm, Def65Support.negLIntegral ];
      simp +decide [Def65Support.negPart, abs_of_nonneg];
  convert h_integrable_pos.sub h_integrable_neg using 1 ; ext ω ; simp +decide [ max_def ] ; split_ifs <;> linarith;

/-- Source reverse proof: Bochner integrability implies textbook integrability. -/
private theorem source_integrable_to_realCoe {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfm : Measurable f)
    (hf : Integrable f μ) : textbookIntegrable μ (fun ω => (f ω : EReal)) := by
  unfold textbookIntegrable
  constructor;
  · refine' lt_of_le_of_lt ( MeasureTheory.lintegral_mono fun ω => _ ) _;
    exact fun ω => ENNReal.ofReal |f ω|;
    · unfold Def65Support.posPart;
      cases abs_cases ( f ω ) <;> simp +decide [ * ];
      rw [ ENNReal.ofReal_eq_zero.mpr ( by linarith ) ] ; norm_num;
    · convert hf.abs.lintegral_lt_top using 1;
  · refine' MeasureTheory.Integrable.lintegral_lt_top _;
    convert hf.neg using 1
    rfl

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfm : Measurable f) :
    textbookIntegrable μ (fun ω => (f ω : EReal)) ↔ Integrable f μ := by
  exact ⟨source_realCoe_to_integrable hfm, source_integrable_to_realCoe hfm⟩
end Thm67Support
