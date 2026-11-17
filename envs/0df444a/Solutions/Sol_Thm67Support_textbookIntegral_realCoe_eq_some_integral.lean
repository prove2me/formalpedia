-- Prove2me | solution 1 for Thm67Support.textbookIntegral_realCoe_eq_some_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:13:11.032064+00:00
-- url     : https://prove2.me/submissions/427b2494-e3df-434e-a58d-c6d233dd593a

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

/-- Exact source calculation identifying the positive and negative Lebesgue parts. -/
private theorem source_integral_pos_neg {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Integrable f μ) :
    ∫⁻ ω, Def65Support.posPart (fun ω => (f ω : EReal)) ω ∂μ = ENNReal.ofReal (∫ ω, max (f ω) 0 ∂μ) ∧ ∫⁻ ω, Def65Support.negPart (fun ω => (f ω : EReal)) ω ∂μ = ENNReal.ofReal (∫ ω, max (-f ω) 0 ∂μ) := by
  constructor <;> rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
  any_goals filter_upwards [ ] using fun _ => le_max_right _ _;
  · congr with ω ; simp +decide [ Def65Support.posPart ];
  · exact hf.pos_part;
  · congr with ω ; simp +decide [ Def65Support.negPart ];
  · exact hf.neg.pos_part;

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Integrable f μ) :
    textbookIntegral μ (fun ω => (f ω : EReal)) = some ((∫ ω, f ω ∂μ : ℝ) : EReal) := by
  unfold textbookIntegral
  simp +decide [Def65Support.posLIntegral, Def65Support.negLIntegral]
  split_ifs with h
  · exfalso
    have hfinite : Def65Support.negLIntegral μ (fun ω => (f ω : EReal)) ≠ ⊤ := by
      convert hf.neg.lintegral_lt_top.ne using 1
      rfl
    exact hfinite h.2
  · have h_pos_neg := source_integral_pos_neg hf
    have hpos : 0 ≤ ∫ ω, max (f ω) 0 ∂μ := integral_nonneg (fun ω => le_max_right _ _)
    have hneg : 0 ≤ ∫ ω, max (-f ω) 0 ∂μ := integral_nonneg (fun ω => le_max_right _ _)
    have hp : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ).toReal = ∫ ω, max (f ω) 0 ∂μ := by
      simpa [Def65Support.posPart, ENNReal.toReal_ofReal hpos] using
        congrArg ENNReal.toReal h_pos_neg.1
    have hn : (∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ).toReal = ∫ ω, max (-f ω) 0 ∂μ := by
      simpa [Def65Support.negPart, ENNReal.toReal_ofReal hneg] using
        congrArg ENNReal.toReal h_pos_neg.2
    simp only [h_pos_neg.1, h_pos_neg.2]
    norm_cast
    rw [MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf, hp, hn]
    simp [ENNReal.ofReal, Real.toNNReal, hpos, hneg, EReal.coe_nnreal_eq_coe_real]
end Thm67Support
