-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.norm_extendByZeroL2
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:04:10.184207+00:00
-- url     : https://prove2.me/submissions/2b29cd70-08a6-4592-a731-33662ea4b70e

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

theorem solution (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖extendByZeroL2 (E := E) (K := K) hKm u‖ = ‖u‖ := by
  classical
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hm : MeasureTheory.MemLp (extendByZeroFun (E := E) (K := K) u)
      (2 : ℝ≥0∞) (volume : Measure E) := by
    simpa [extendByZeroFun] using
      (MeasureTheory.memLp_indicator_iff_restrict (μ := (volume : Measure E))
        (p := (2 : ℝ≥0∞)) (s := K) (f := fun x : E => u x) hKm).2
          (MeasureTheory.Lp.memLp u)
  have h₁ :
      (extendByZeroL2 (E := E) (K := K) hKm u : E → ℝ) =ᵐ[(volume : Measure E)]
        extendByZeroFun (E := E) (K := K) u := by
    exact hm.coeFn_toLp
  have h₂ :
      (((MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ)
        (p := (2 : ℝ≥0∞)) (s := K) hKm) u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) volume) : E → ℝ) =ᵐ[volume]
        extendByZeroFun (E := E) (K := K) u := by
    simpa [MeasureTheory.Lp.extendByZeroₗᵢ, MeasureTheory.Lp.extendByZeroₗ,
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.extendByZeroFun] using
      (MeasureTheory.Lp.extendByZeroFun_coe (μ := (volume : Measure E)) (E := ℝ)
        (p := (2 : ℝ≥0∞)) (s := K) hKm u)
  calc
    ‖extendByZeroL2 (E := E) (K := K) hKm u‖ =
        ‖(MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ)
          (p := (2 : ℝ≥0∞)) (s := K) hKm) u‖ := by
      exact congrArg norm (MeasureTheory.Lp.ext (h₁.trans h₂.symm))
    _ = ‖u‖ := LinearIsometry.norm_map _ _
