-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothFun_sub_extendByZeroFun_sq_le_integral_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:40:41.329143+00:00
-- url     : https://prove2.me/submissions/6cd6b6d6-17f3-47ef-bf17-aebb786dd29b

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
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_isProbabilityMeasure_kernelMeasure
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothFun_eq_integral_kernelMeasure
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_sq_integral_le_integral_sq_of_isProbabilityMeasure
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_extendByZeroL2_ae_eq

section
namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness
open scoped ENNReal MeasureTheory Topology Convolution
open MeasureTheory Set
noncomputable section
section Volume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] instMeasurableSpaceApproximation instBorelSpaceApproximation instOpensMeasurableSpaceApproximation instMeasurableAddApproximation instMeasurableNegApproximation
variable {K : Set E} (hK : IsCompact K) (hKm : MeasurableSet K)
variable (ψ : E → ℝ)
private lemma kernelMeasure_le_smul_volume (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ kernelMeasure (E := E) ψ ≤ c • (volume : Measure E) := by
  classical
  obtain ⟨C, hC⟩ := hψcs.exists_bound_of_continuous hψc
  refine ⟨ENNReal.ofReal C, by simp, ?_⟩
  refine (Measure.le_iff).2 ?_
  intro s hs
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (ψ 0)) (hC 0)
  have hψle : ∀ x, ENNReal.ofReal (ψ x) ≤ ENNReal.ofReal C := by
    intro x
    have hx : ψ x ≤ C := by
      have hx' : ‖ψ x‖ ≤ C := hC x
      -- `ψ ≥ 0`, so `‖ψ x‖ = ψ x`.
      simpa [Real.norm_eq_abs, abs_of_nonneg (hψ0 x)] using hx'
    exact ENNReal.ofReal_le_ofReal hx
  -- Unfold `withDensity` and bound the density by the constant `ENNReal.ofReal C`.
  simp only [kernelMeasure, MeasureTheory.withDensity_apply, hs]
  have hle :
      (∫⁻ x in s, ENNReal.ofReal (ψ x) ∂(volume : Measure E)) ≤
        ∫⁻ x in s, ENNReal.ofReal C ∂(volume : Measure E) := by
    refine MeasureTheory.lintegral_mono ?_
    intro x
    exact hψle x
  refine hle.trans ?_
  simp
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
theorem _root_.solution
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    (smoothFun (E := E) (K := K) ψ u x - extendByZeroFun (E := E) (K := K) u x) ^ 2 ≤
      ∫ t,
        (extendByZeroFun (E := E) (K := K) u (x - t) - extendByZeroFun (E := E) (K := K) u x) ^ 2
          ∂kernelMeasure (E := E) ψ := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  have : MeasureTheory.IsProbabilityMeasure μ :=
    isProbabilityMeasure_kernelMeasure (E := E) (ψ := ψ) hψc hψcs hψ0 hψint
  have : MeasureTheory.IsFiniteMeasure μ := by infer_instance
  rcases kernelMeasure_le_smul_volume (E := E) (ψ := ψ) hψc hψcs hψ0 with ⟨c, hc_top, hμle⟩
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  have hf_vol : MeasureTheory.MemLp f (2 : ℝ≥0∞) (volume : Measure E) := by
    -- Use the `L²` packaging of `extendByZeroFun` and the AE bridge.
    let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
    have hF : MeasureTheory.MemLp (fun x : E => (F : E → ℝ) x) (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp F
    have hF_ae : (fun x : E => (F : E → ℝ) x) =ᵐ[(volume : Measure E)] f :=
      extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
    exact (MeasureTheory.memLp_congr_ae hF_ae).1 hF
  have hmp :
      MeasureTheory.MeasurePreserving (fun t : E => x - t)
        (volume : Measure E) (volume : Measure E) := by
    -- `t ↦ x - t = (-t) + x` is measure-preserving for Lebesgue (Haar) measure.
    have hneg :
        MeasureTheory.MeasurePreserving (Neg.neg : E → E)
          (volume : Measure E) (volume : Measure E) :=
      (volume : Measure E).measurePreserving_neg
    have hadd :
        MeasureTheory.MeasurePreserving (fun y : E => y + x)
          (volume : Measure E) (volume : Measure E) :=
      MeasureTheory.measurePreserving_add_right
        (μ := (volume : Measure E)) x
    have hcomp : ((fun y : E => y + x) ∘ fun t : E => -t) = fun t : E => x - t := by
      funext t
      simp [sub_eq_add_neg, add_comm]
    have := hadd.comp hneg
    rwa [hcomp] at this
  have hf_shift_vol :
      MeasureTheory.MemLp (fun t : E => f (x - t))
        (2 : ℝ≥0∞) (volume : Measure E) :=
    hf_vol.comp_measurePreserving hmp
  have hf_shift :
      MeasureTheory.MemLp (fun t : E => f (x - t))
        (2 : ℝ≥0∞) μ := by
    exact MeasureTheory.MemLp.of_measure_le_smul
      (μ := (volume : Measure E)) (μ' := μ) (c := c)
      hc_top hμle hf_shift_vol
  have hf_const : MeasureTheory.MemLp (fun _ : E => f x) (2 : ℝ≥0∞) μ :=
    MeasureTheory.memLp_const (μ := μ) (c := f x)
  have hg : MeasureTheory.MemLp (fun t : E => f (x - t) - f x) (2 : ℝ≥0∞) μ :=
    hf_shift.sub hf_const
  have hsmooth :
      smoothFun (E := E) (K := K) ψ u x = ∫ t, f (x - t) ∂μ := by
    simpa [μ, f] using smoothFun_eq_integral_kernelMeasure (E := E) (K := K) (ψ := ψ) hψc hψ0 u x
  have hdiff :
      smoothFun (E := E) (K := K) ψ u x - f x = ∫ t, (f (x - t) - f x) ∂μ := by
    have hconst : (∫ _t : E, f x ∂μ) = f x := by
      simp [MeasureTheory.integral_const]
    have hint : MeasureTheory.Integrable (fun t : E => f (x - t)) μ :=
      hf_shift.integrable (by norm_num)
    have :
        (∫ t, f (x - t) ∂μ) - (∫ _t : E, f x ∂μ) =
          ∫ t, (f (x - t) - f x) ∂μ := by
      simpa using (MeasureTheory.integral_sub hint (MeasureTheory.integrable_const (f x))).symm
    simpa [hsmooth, hconst] using this
  -- Apply Jensen/variance inequality to `t ↦ f(x - t) - f(x)`.
  have hJ :=
    sq_integral_le_integral_sq_of_isProbabilityMeasure
      (μ := μ) (f := fun t : E => f (x - t) - f x) hg
  simpa [hdiff, μ, f] using hJ
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
