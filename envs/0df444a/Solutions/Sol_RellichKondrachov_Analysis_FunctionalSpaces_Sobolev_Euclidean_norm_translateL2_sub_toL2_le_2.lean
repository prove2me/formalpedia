-- Prove2me | solution 2 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.norm_translateL2_sub_toL2_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:41:50.005076+00:00
-- url     : https://prove2.me/submissions/fac7a2af-62d9-462e-857a-53bbce27584b

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_enorm_translateL2_sub_toL2_le

set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceTranslationEstimateL2
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceTranslationEstimateL2
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceTranslationEstimateL2
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableAddTranslationEstimateL2
attribute [local instance] instMeasurableSpaceTranslationEstimateL2 instBorelSpaceTranslationEstimateL2 instOpensMeasurableSpaceTranslationEstimateL2 instMeasurableAddTranslationEstimateL2
variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
theorem _root_.solution (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ ≤
      ‖a‖ * ‖toL2Grad (μ := μ) (E := E) f‖ := by
  have h := enorm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hA_ne_top :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by
    simp [enorm]
  have hGrad_ne_top :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by
    simp [enorm]
  have hB_ne_top : (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by
    refine ENNReal.mul_ne_top ?_ hGrad_ne_top
    simp [enorm]
  have h' :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ).toReal ≤
        (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ).toReal := by
    exact (ENNReal.toReal_le_toReal hA_ne_top hB_ne_top).2 h
  simpa only [ENNReal.toReal_mul, toReal_enorm] using h'
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
