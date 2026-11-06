-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.support_smoothFun_subset_add_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:03:22.670201+00:00
-- url     : https://prove2.me/submissions/67519518-537c-4e12-8238-8d4c8311f52b

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
variable (ψ : E → ℝ)

theorem solution
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    Function.support (smoothFun (E := E) (K := K) ψ u) ⊆ K + tsupport ψ := by
  have hconv :
      Function.support (smoothFun (E := E) (K := K) ψ u) ⊆
        Function.support (extendByZeroFun (E := E) (K := K) u) + Function.support ψ := by
    simpa [smoothFun] using
      (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)
        (μ := (volume : Measure E))
        (f := extendByZeroFun (E := E) (K := K) u) (g := ψ))
  exact hconv.trans <| add_subset_add (by simp [extendByZeroFun]) (subset_tsupport ψ)
