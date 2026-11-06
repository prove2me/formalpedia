-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.kernelMeasure_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:52:18.584847+00:00
-- url     : https://prove2.me/submissions/1e0508ba-0989-45c0-952b-d3987d3c348f

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
theorem _root_.solution (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) :
    kernelMeasure (E := E) ψ Set.univ = 1 := by
  have hψi : MeasureTheory.Integrable ψ (volume : Measure E) :=
    Continuous.integrable_of_hasCompactSupport (μ := (volume : Measure E)) hψc hψcs
  have hψae : (MeasureTheory.ae (volume : Measure E)).EventuallyLE 0 ψ :=
    Filter.Eventually.of_forall hψ0
  have hlin :
      (∫⁻ x, ENNReal.ofReal (ψ x) ∂(volume : Measure E)) =
        ENNReal.ofReal (∫ x, ψ x ∂(volume : Measure E)) := by
    symm
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hψi hψae
  -- `withDensity` on `univ` is the `lintegral` of the density.
  have hwd :
      kernelMeasure (E := E) ψ Set.univ =
        ∫⁻ x, ENNReal.ofReal (ψ x) ∂(volume : Measure E) := by
    simp [kernelMeasure, MeasureTheory.withDensity_apply, MeasurableSet.univ]
  -- Conclude using `∫ ψ = 1`.
  simpa [hψint] using (hwd.trans hlin)
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
