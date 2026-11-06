-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:38:14.31145+00:00
-- url     : https://prove2.me/submissions/a1dc4988-d9c1-4145-a33e-5335c1ea0097

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_kernelMeasure_univ

section
namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
section Volume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] instMeasurableSpaceEL2CompactnessTranslationIntegral instBorelSpaceEL2CompactnessTranslationIntegral instOpensMeasurableSpaceEL2CompactnessTranslationIntegral instMeasurableAddEL2CompactnessTranslationIntegral instMeasurableNegEL2CompactnessTranslationIntegral
variable {ψ : E → ℝ}
private lemma kernelMeasure_compl_ball_eq_zero_of_tsupport_subset {deltaLoss : ℝ}
    (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss) :
    kernelMeasure (E := E) ψ ((Metric.ball (0 : E) deltaLoss)ᶜ) = 0 := by
  classical
  have hψzero : ∀ x : E, x ∈ (Metric.ball (0 : E) deltaLoss)ᶜ → ψ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ψ := by
      intro hx_ts
      exact hx (hψsupp hx_ts)
    exact image_eq_zero_of_notMem_tsupport (f := ψ) hx'
  have hmeas : MeasurableSet ((Metric.ball (0 : E) deltaLoss)ᶜ) :=
    (measurableSet_ball : MeasurableSet (Metric.ball (0 : E) deltaLoss)).compl
  have hEq :
      Set.EqOn (fun x : E => ENNReal.ofReal (ψ x)) 0 ((Metric.ball (0 : E) deltaLoss)ᶜ) := by
    intro x hx
    simp [hψzero x hx]
  -- Expand `kernelMeasure` and note the density is identically `0` on the set.
  simp [kernelMeasure, MeasureTheory.withDensity_apply, hmeas,
    MeasureTheory.setLIntegral_eq_zero
      (μ := (volume : Measure E))
      (s := (Metric.ball (0 : E) deltaLoss)ᶜ) hmeas hEq]
end Volume
end
end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end

set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceEL2CompactnessTranslationIntegral
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceEL2CompactnessTranslationIntegral
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpaceEL2CompactnessTranslationIntegral
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableAddEL2CompactnessTranslationIntegral
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableNegEL2CompactnessTranslationIntegral
attribute [local instance] instMeasurableSpaceEL2CompactnessTranslationIntegral instBorelSpaceEL2CompactnessTranslationIntegral instOpensMeasurableSpaceEL2CompactnessTranslationIntegral instMeasurableAddEL2CompactnessTranslationIntegral instMeasurableNegEL2CompactnessTranslationIntegral
variable {ψ : E → ℝ}
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
theorem _root_.solution
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    {deltaLoss η : ℝ} (hη : 0 ≤ η) (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss)
    (F : (E →₂[(volume : Measure E)] ℝ))
    (hmod :
      ∀ t : E, t ∈ Metric.ball (0 : E) deltaLoss →
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η) :
    ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
      ∂kernelMeasure (E := E) ψ ≤ η ^ 2 := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  have : MeasureTheory.IsProbabilityMeasure μ :=
    ⟨kernelMeasure_univ (E := E) (ψ := ψ) hψc hψcs hψ0 hψint⟩
  have hμzero : μ ((Metric.ball (0 : E) deltaLoss)ᶜ) = 0 := by
    simpa [μ] using kernelMeasure_compl_ball_eq_zero_of_tsupport_subset (E := E) (ψ := ψ) hψsupp
  have hAE_ball : (Metric.ball (0 : E) deltaLoss) ∈ MeasureTheory.ae μ :=
    (MeasureTheory.mem_ae_iff.2 hμzero)
  -- On `Metric.ball 0 deltaLoss`, the squared translation error is bounded by `η²`.
  have hAE_bound :
      ∀ᵐ t : E ∂μ,
        ‖‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2‖ ≤ η ^ 2 := by
    filter_upwards [hAE_ball] with t ht
    have hle : ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η := hmod t ht
    have hsq :
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ≤ η ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hη).2 hle
    have hnonneg : 0 ≤ ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 :=
      sq_nonneg _
    have hηnonneg : 0 ≤ η ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hηnonneg] using hsq
  have hnorm_int :
      ‖∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ‖ ≤ η ^ 2 * μ.real Set.univ := by
    simpa using
      (MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun t : E => ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2)
        (C := η ^ 2) hAE_bound)
  have hμreal : μ.real Set.univ = 1 := by
    -- `μ` is a probability measure.
    simp [MeasureTheory.measureReal_def]
  have hnonneg_int :
      0 ≤ ∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ := by
    refine MeasureTheory.integral_nonneg ?_
    intro t
    exact sq_nonneg _
  -- Use `|∫ f| = ∫ f` for a nonnegative integrand.
  have habs :
      |∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ| ≤ η ^ 2 := by
    have := hnorm_int
    -- Replace `‖·‖` by `abs` in `ℝ` and simplify `μ.real univ = 1`.
    simpa [Real.norm_eq_abs, hμreal, mul_one] using this
  simpa [abs_of_nonneg hnonneg_int, μ] using habs
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
