-- Prove2me | solution 1 for Thm66Support.complexTextbookIntegrable_iff_complexAbsIntegral_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:15:37.34075+00:00
-- url     : https://prove2.me/submissions/a7f73cfd-8f06-4814-abb3-83e4930555f0

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

theorem solution {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ) (hZm : Measurable Z) :
    Thm66Support.complexTextbookIntegrable μ Z ↔ Thm66Support.complexAbsIntegral μ Z < ⊤ := by
  constructor
  · intro hZ
    have h_pointwise :
        (fun ω => ENNReal.ofReal ‖Z ω‖) ≤
          fun ω => ENNReal.ofReal |(Z ω).re| + ENNReal.ofReal |(Z ω).im| := by
      intro ω
      simpa [ENNReal.ofReal_add, abs_nonneg, add_comm, add_left_comm, add_assoc] using
        ENNReal.ofReal_le_ofReal (Complex.norm_le_abs_re_add_abs_im (Z ω))
    have h_meas_re : Measurable fun ω => ENNReal.ofReal |(Z ω).re| := by
      apply Measurable.ennreal_ofReal
      simpa [Function.comp_def] using
        continuous_abs.measurable.comp
          (Complex.continuous_re.measurable.comp hZm)
    have h_rhs_top :
        ∫⁻ ω, (ENNReal.ofReal |(Z ω).re| + ENNReal.ofReal |(Z ω).im|) ∂μ < ⊤ := by
      have hsum :
          ∫⁻ ω, (ENNReal.ofReal |(Z ω).re| + ENNReal.ofReal |(Z ω).im|) ∂μ =
            realPartAbsIntegral μ Z + imagPartAbsIntegral μ Z := by
        rw [lintegral_add_left h_meas_re]
        rfl
      rw [hsum]
      exact ENNReal.add_lt_top.mpr hZ
    exact lt_of_le_of_lt (lintegral_mono h_pointwise) h_rhs_top
  · intro hAbs
    constructor
    · refine lt_of_le_of_lt ?_ hAbs
      apply lintegral_mono
      intro ω
      exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm (Z ω))
    · refine lt_of_le_of_lt ?_ hAbs
      apply lintegral_mono
      intro ω
      exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm (Z ω))
end Thm66Support
