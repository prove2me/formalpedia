-- Prove2me | solution 1 for ProbabilityTheory.integral_sq_levySlice_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:01:48.370292+00:00
-- url     : https://prove2.me/submissions/6941272c-6d5e-4c25-b700-b52e27da6302

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_levyTruncationSeq_spec
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_sigmaFinite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem solution :
    ∀ {ν : Measure ℝ} (hν : IsLevyMeasure ν) (j : ℕ),
      ∫ x in levySlice hν j, x ^ 2 ∂ν ≤ ((16 : ℝ)⁻¹) ^ j := by
  intro ν hν j
  haveI : SigmaFinite ν := hν.sigmaFinite
  have hsliceSubset : levySlice hν j ⊆ Set.Ioo (-1 : ℝ) 1 := by
    change (levyAnnulus (levyTruncationSeq hν (j + 1)) \
      levyAnnulus (levyTruncationSeq hν j)) ⊆ Set.Ioo (-1 : ℝ) 1
    exact Set.sdiff_subset.trans Set.inter_subset_left
  have hsliceMeas : MeasurableSet (levySlice hν j) :=
    (measurableSet_levyAnnulus _).diff (measurableSet_levyAnnulus _)
  have hsliceSubsetDiff :
      levySlice hν j ⊆ Set.Ioo (-1 : ℝ) 1 \ levyAnnulus (levyTruncationSeq hν j) := by
    intro x hx
    exact ⟨hx.1.1, hx.2⟩
  have hlintegral (A : Set ℝ) (hA : MeasurableSet A)
      (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) :
      ∫⁻ x in A, ENNReal.ofReal (x ^ 2) ∂ν < ⊤ := by
    refine lt_of_le_of_lt ?_ hν.2
    rw [← lintegral_indicator hA]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      obtain ⟨h1, h2⟩ := hAsub hx
      exact ENNReal.ofReal_le_ofReal (le_min (by nlinarith) le_rfl)
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hintegrable (A : Set ℝ) (hA : MeasurableSet A)
      (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) :
      IntegrableOn (fun x : ℝ => x ^ 2) A ν := by
    refine ⟨(by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg x)]
    exact hlintegral A hA hAsub
  have hofReal (A : Set ℝ) (hA : MeasurableSet A)
      (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) :
      ENNReal.ofReal (∫ x in A, x ^ 2 ∂ν)
        = ∫⁻ x in A, ENNReal.ofReal (x ^ 2) ∂ν :=
    ofReal_integral_eq_lintegral_ofReal (hintegrable A hA hAsub)
      (ae_of_all _ fun x => sq_nonneg x)
  have hlint : (∫⁻ x in levySlice hν j, ENNReal.ofReal (x ^ 2) ∂ν)
      ≤ ∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus (levyTruncationSeq hν j),
          ENNReal.ofReal (x ^ 2) ∂ν :=
    lintegral_mono' (Measure.restrict_mono (hsliceSubsetDiff) le_rfl) le_rfl
  have hbound : (∫⁻ x in levySlice hν j, ENNReal.ofReal (x ^ 2) ∂ν)
      ≤ (16 : ℝ≥0∞)⁻¹ ^ j :=
    hlint.trans ((levyTruncationSeq_spec hν).2 j)
  have hne : (16 : ℝ≥0∞)⁻¹ ^ j ≠ ⊤ :=
    (ENNReal.pow_lt_top (ENNReal.inv_lt_top.mpr (by norm_num))).ne
  calc ∫ x in levySlice hν j, x ^ 2 ∂ν
      = (ENNReal.ofReal (∫ x in levySlice hν j, x ^ 2 ∂ν)).toReal :=
        (ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg x)).symm
    _ = (∫⁻ x in levySlice hν j, ENNReal.ofReal (x ^ 2) ∂ν).toReal := by
        rw [hofReal _ hsliceMeas hsliceSubset]
    _ ≤ ((16 : ℝ≥0∞)⁻¹ ^ j).toReal := ENNReal.toReal_mono hne hbound
    _ = ((16 : ℝ)⁻¹) ^ j := by
        rw [ENNReal.toReal_pow, ENNReal.toReal_inv]
        norm_num