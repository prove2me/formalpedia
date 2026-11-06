-- Prove2me | solution 2 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.integral_kernelMeasure_eq_integral_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:38:01.273149+00:00
-- url     : https://prove2.me/submissions/916e5837-559d-4f06-9847-2a9fd576ca3c

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation

set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
open scoped ENNReal MeasureTheory Topology Convolution
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceApproximation
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceApproximation
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpaceApproximation
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableAddApproximation
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableNegApproximation
attribute [local instance] instMeasurableSpaceApproximation instBorelSpaceApproximation instOpensMeasurableSpaceApproximation instMeasurableAddApproximation instMeasurableNegApproximation
variable {K : Set E} (hK : IsCompact K) (hKm : MeasurableSet K)
variable (ψ : E → ℝ)
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
theorem _root_.solution (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (g : E → ℝ) :
    (∫ x, g x ∂kernelMeasure (E := E) ψ) =
      ∫ x, (ψ x) • (g x) ∂(volume : Measure E) := by
  have hmeas : Measurable fun x => ENNReal.ofReal (ψ x) :=
    (hψc.measurable.ennreal_ofReal : Measurable fun x => ENNReal.ofReal (ψ x))
  have htop :
      (MeasureTheory.ae (volume : Measure E)).Eventually
        (fun x => ENNReal.ofReal (ψ x) < (⊤ : ℝ≥0∞)) :=
    Filter.Eventually.of_forall (fun _ => by simp)
  have hwd :=
    (integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure E))
      (f := fun x => ENNReal.ofReal (ψ x)) hmeas htop g)
  have hwd' :
      (∫ x, g x ∂kernelMeasure (E := E) ψ) =
        ∫ x, (ENNReal.ofReal (ψ x)).toReal • (g x) ∂(volume : Measure E) := by
    simpa [kernelMeasure] using hwd
  -- Simplify `toReal (ofReal _)` using `ψ ≥ 0`.
  refine hwd'.trans ?_
  refine integral_congr_ae ?_
  refine ae_of_all _ (fun x => ?_)
  have hx : (ENNReal.ofReal (ψ x)).toReal = ψ x :=
    ENNReal.toReal_ofReal (hψ0 x)
  -- After rewriting `toReal (ofReal _)`, both sides are definitional.
  simp [hx]
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
