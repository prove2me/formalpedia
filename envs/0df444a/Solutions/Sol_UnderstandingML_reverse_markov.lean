-- Prove2me | solution 1 for UnderstandingML.reverse_markov
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T13:21:59.249031+00:00
-- url     : https://prove2.me/submissions/7160ef22-659d-45cc-8dca-daf72532eed5

import Definitions.Def_UnderstandingML_Framework
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory

namespace UnderstandingML

/-- For `Z ∈ [0,1]` a.s. and any `t`: `E[Z] ≤ t + (1 - t) P[Z > t]`. -/
theorem reverse_markov_aux {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω)
    [IsProbabilityMeasure D] (θ : Ω → ℝ) (hθ : Measurable θ)
    (hrange : ∀ᵐ ω ∂D, θ ω ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    (∫ ω, θ ω ∂D) ≤ t + (1 - t) * (D {ω | t < θ ω}).toReal := by
  have hS : MeasurableSet {ω | t < θ ω} := measurableSet_lt measurable_const hθ
  have hint : Integrable θ D := by
    refine Integrable.of_bound (C := 1) hθ.aestronglyMeasurable ?_
    filter_upwards [hrange] with ω hω
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hω.1], hω.2⟩
  have hind : Integrable (fun ω => t + (1 - t) * ({ω | t < θ ω}.indicator (fun _ => (1 : ℝ)) ω)) D :=
    (integrable_const t).add ((integrable_const (1 : ℝ)).indicator hS |>.const_mul (1 - t))
  have hle : ∀ᵐ ω ∂D, θ ω ≤ t + (1 - t) * ({ω | t < θ ω}.indicator (fun _ => (1 : ℝ)) ω) := by
    filter_upwards [hrange] with ω hω
    by_cases h : t < θ ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | t < θ ω} from h)]
      linarith [hω.2]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | t < θ ω} from h)]
      linarith [not_lt.mp h]
  calc (∫ ω, θ ω ∂D)
      ≤ ∫ ω, (t + (1 - t) * ({ω | t < θ ω}.indicator (fun _ => (1 : ℝ)) ω)) ∂D :=
        integral_mono_ae hint hind hle
    _ = t + (1 - t) * (D {ω | t < θ ω}).toReal := by
        rw [integral_add (integrable_const t)
          ((integrable_const (1 : ℝ)).indicator hS |>.const_mul (1 - t)),
          integral_const_mul, integral_indicator hS, setIntegral_const]
        simp [measureReal_def]

end UnderstandingML

open UnderstandingML

theorem solution {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
    (θ : Ω → ℝ) (hθ : Measurable θ) (hrange : ∀ᵐ ω ∂D, θ ω ∈ Set.Icc (0 : ℝ) 1) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    ((∫ ω, θ ω ∂D) - (1 - a)) / a ≤ (D {ω | 1 - a < θ ω}).toReal ∧
    ((∫ ω, θ ω ∂D) - a) / (1 - a) ≤ (D {ω | a < θ ω}).toReal ∧
    (∫ ω, θ ω ∂D) - a ≤ (D {ω | a < θ ω}).toReal := by
  have h1 := reverse_markov_aux D θ hθ hrange (1 - a)
  have h2 := reverse_markov_aux D θ hθ hrange a
  have hp : 0 ≤ (D {ω | a < θ ω}).toReal := ENNReal.toReal_nonneg
  have hp1 : (D {ω | a < θ ω}).toReal ≤ 1 := by
    have := prob_le_one (μ := D) (s := {ω | a < θ ω})
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ ha0]
    have : 1 - (1 - a) = a := by ring
    rw [this] at h1
    linarith
  · rw [div_le_iff₀ (by linarith)]
    linarith
  · nlinarith
