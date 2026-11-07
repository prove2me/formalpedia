-- Prove2me | solution 1 for StatUnlearn.tof_le_tof_comp
-- status  : ACCEPTED   (prove)
-- author  : @2017Advanced@
-- created : 2026-11-06T20:18:19.819587+00:00
-- url     : https://prove2.me/submissions/6046685e-4555-465d-846a-437d106db13c

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_su_tof
open MeasureTheory ProbabilityTheory
open StatUnlearn

theorem solution {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]
    (κ : Kernel W V) [IsMarkovKernel κ] (P Q : Measure W) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (t : ℝ) (ht : 0 ≤ t) :
    tof P Q t ≤ tof (κ ∘ₘ P) (κ ∘ₘ Q) t := by
  -- iterated-integral form of the push-forward
  have integral_comp_kernel : ∀ (P' : Measure W) (f : V → ℝ), Integrable f (κ ∘ₘ P') →
      ∫ v, f v ∂(κ ∘ₘ P') = ∫ w, ∫ v, f v ∂(κ w) ∂P' := by
    intro P' f hf
    have key := Kernel.integral_comp (κ := Kernel.const Unit P') (η := κ) (a := ()) (f := f)
      (by simpa using hf)
    simpa [Kernel.comp_const] using key
  -- `0` is a lower bound for the achievable errors of `(P,Q)`
  have hbdd : BddBelow {β : ℝ | ∃ φ : W → ℝ, Measurable φ ∧ (∀ w, φ w ∈ Set.Icc (0 : ℝ) 1) ∧
      (∫ w, φ w ∂P) ≤ t ∧ β = ∫ w, (1 - φ w) ∂Q} := by
    refine ⟨0, ?_⟩
    rintro β ⟨φ, -, hφ01, -, rfl⟩
    refine integral_nonneg_of_ae ?_
    filter_upwards with w
    exact sub_nonneg.mpr (hφ01 w).2
  -- the post-processed set is nonempty
  have hne : ({β : ℝ | ∃ φ : V → ℝ, Measurable φ ∧ (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) ∧
      (∫ v, φ v ∂(κ ∘ₘ P)) ≤ t ∧ β = ∫ v, (1 - φ v) ∂(κ ∘ₘ Q)}).Nonempty := by
    refine ⟨1, fun _ => 0, measurable_const, fun v => ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
    · simp; exact ht
    · have : ∀ v : V, (1 : ℝ) - 0 = 1 := by intro v; norm_num
      simp only [this]
      rw [integral_const]; simp [Measure.real]
  refine csInf_le_csInf hbdd hne ?_
  rintro β ⟨φ, hφm, hφ01, hφα, rfl⟩
  -- the pulled-back test
  have hint : ∀ w, Integrable (fun v => φ v) (κ w) := fun w =>
    Integrable.of_bound hφm.aestronglyMeasurable 1 (by
      filter_upwards with v
      rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 v).1]
      exact (hφ01 v).2)
  have hInt : Integrable (fun v => φ v) (κ ∘ₘ P) :=
    Integrable.of_bound hφm.aestronglyMeasurable 1 (by
      filter_upwards with v
      rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 v).1]
      exact (hφ01 v).2)
  have hInt2 : Integrable (fun v => 1 - φ v) (κ ∘ₘ Q) :=
    Integrable.of_bound (measurable_const.sub hφm).aestronglyMeasurable 1 (by
      filter_upwards with v
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [(hφ01 v).1, (hφ01 v).2])
  refine ⟨fun w => ∫ v, φ v ∂(κ w), ?_, ?_, ?_, ?_⟩
  · exact hφm.stronglyMeasurable.integral_kernel.measurable
  · -- the pulled-back function takes values in `[0,1]`
    intro w
    exact ⟨MeasureTheory.integral_nonneg (fun v => (hφ01 v).1), by
      have := integral_mono (hint w) (integrable_const (1 : ℝ)) (fun v => (hφ01 v).2)
      simpa using this⟩
  · -- same type-I error
    simp only []
    rw [← integral_comp_kernel P (fun v => φ v) hInt]
    exact hφα
  · -- same type-II error
    simp only []
    rw [integral_comp_kernel Q (fun v => 1 - φ v) hInt2]
    congr 1
    funext w
    rw [integral_sub (integrable_const 1) (hint w), integral_const]
    simp [Measure.real]


