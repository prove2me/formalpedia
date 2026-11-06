-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.extendByZeroL2_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:40:41.279412+00:00
-- url     : https://prove2.me/submissions/f7362324-b21e-4e10-b60d-5ec1386d82c6

import Definitions.Def_RellichKondrachov_MeasureTheory_Function_LpSpace_Restrict
import Mathlib.Analysis.Convolution
import Mathlib.Topology.Algebra.Support
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing

set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceSmoothing1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceSmoothing1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpaceSmoothing1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableAddSmoothing1
variable {K : Set E}
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
theorem _root_.solution (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (extendByZeroL2 (E := E) (K := K) hKm u : E → ℝ) =ᵐ[(volume : Measure E)]
      extendByZeroFun (E := E) (K := K) u := by
  classical
  simp [extendByZeroL2, MeasureTheory.MemLp.coeFn_toLp]
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
