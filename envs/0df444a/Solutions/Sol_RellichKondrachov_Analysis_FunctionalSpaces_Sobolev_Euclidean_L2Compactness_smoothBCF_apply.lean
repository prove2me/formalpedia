-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:39:29.825063+00:00
-- url     : https://prove2.me/submissions/60ee4370-7fa2-4d0f-a080-7cbbd5a6032f

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness

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
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceEL2CompactnessCompactness
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceEL2CompactnessCompactness
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpaceEL2CompactnessCompactness
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableAddEL2CompactnessCompactness
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableNegEL2CompactnessCompactness
variable {K : Set E}
variable {ψ : E → ℝ}
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
theorem _root_.solution (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
    (x : ↥(Kψ (K := K) (ψ := ψ))) :
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x =
      smoothFun (E := E) (K := K) ψ u x := by
  rfl
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
