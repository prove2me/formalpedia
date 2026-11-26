-- Prove2me | solution 1 for aemeasurable_of_analytic_sublevels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:17.617829+00:00
-- url     : https://prove2.me/submissions/b3edfd17-585e-4b67-a1e9-4fa4e56d6e71

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Theorems.Thm_MeasureTheory_AnalyticSet_nullMeasurableSet


set_option autoImplicit false
open Set Topology MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal
noncomputable section
theorem _root_.solution
    {V : Type*} [TopologicalSpace V] [PolishSpace V]
    [MeasurableSpace V] [BorelSpace V] {g : V → ℝ≥0∞}
    (hg : ∀ c, AnalyticSet {v | g v < c})
    (μ : Measure V) [IsFiniteMeasure μ] :
    AEMeasurable g μ := by
  have hnm : NullMeasurable g μ := by
    intro s hs
    rw [BorelSpace.measurable_eq (α := ℝ≥0∞),
      borel_eq_generateFrom_Iio ℝ≥0∞] at hs
    induction hs with
    | basic u hu =>
      obtain ⟨c, rfl⟩ := hu
      have hpre : g ⁻¹' Iio c = {v | g v < c} := rfl
      rw [hpre]
      exact (hg c).nullMeasurableSet μ
    | empty =>
      rw [preimage_empty]
      exact MeasurableSet.empty.nullMeasurableSet
    | compl u _ ih =>
      rw [preimage_compl]
      exact ih.compl
    | iUnion u _ ih =>
      rw [preimage_iUnion]
      exact NullMeasurableSet.iUnion ih
  exact hnm.aemeasurable
