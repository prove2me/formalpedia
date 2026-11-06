-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.norm_sq_translateL2_sub_extendByZeroL2_eq_integral_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:38:09.03202+00:00
-- url     : https://prove2.me/submissions/892fa832-026d-47ff-9f7d-8ffec04f0ec1

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
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_extendByZeroL2_ae_eq
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_translateL2_ae_eq

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
private lemma norm_sq_eq_integral_sq (v : (E →₂[(volume : Measure E)] ℝ)) :
    ‖v‖ ^ 2 = ∫ x, (v x) ^ 2 ∂(volume : Measure E) := by
  have hn : ‖v‖ ^ 2 = RCLike.re (inner ℝ v v) :=
    norm_sq_eq_re_inner (𝕜 := ℝ) v
  -- Unfold the `L²` inner product as an integral; for `ℝ`, `re` is the identity.
  rw [hn]
  -- `L²` inner product is an integral of pointwise inner products.
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ) (μ := (volume : Measure E)) v v]
  -- For `ℝ`, `RCLike.re` is the identity and `inner` simplifies to a square.
  simp [pow_two]
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
theorem _root_.solution (t : E)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖(translateL2 (μ := (volume : Measure E)) (-t))
        (extendByZeroL2 (E := E) (K := K) hKm u)
        - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 =
      ∫ x,
        (extendByZeroFun (E := E) (K := K) u (x - t) - extendByZeroFun (E := E) (K := K) u x) ^ 2
          ∂(volume : Measure E) := by
  classical
  let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  have hF_ae : (F : E → ℝ) =ᵐ[(volume : Measure E)] f :=
    extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
  -- Translate AE equality along `x ↦ x - t`.
  have hF_shift :
      (fun x : E => (F : E → ℝ) (x - t)) =ᵐ[(volume : Measure E)] fun x => f (x - t) := by
    have hmp :
        MeasureTheory.MeasurePreserving (fun x : E => x - t)
          (volume : Measure E) (volume : Measure E) :=
      MeasureTheory.measurePreserving_sub_right (μ := (volume : Measure E)) t
    exact (hmp.quasiMeasurePreserving.ae_eq_comp hF_ae)
  -- TranslateL2 gives `F(x - t)` a.e.
  have htrans :
      ((translateL2 (μ := (volume : Measure E)) (-t)) F : E → ℝ) =ᵐ[(volume : Measure E)]
        fun x => (F : E → ℝ) (x - t) := by
    simpa [sub_eq_add_neg] using (translateL2_ae_eq (μ := (volume : Measure E)) (-t) F)
  have htrans' :
      ((translateL2 (μ := (volume : Measure E)) (-t)) F : E → ℝ) =ᵐ[(volume : Measure E)]
        fun x => f (x - t) := by
    exact htrans.trans hF_shift
  have hdiff :
      (fun x => ((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x) =ᵐ[(volume : Measure E)]
        fun x => f (x - t) - f x := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub ((translateL2 (μ := (volume : Measure E)) (-t)) F) F,
      htrans', hF_ae] with x hxsub hx1 hx2
    -- `Lp.coeFn_sub` gives the pointwise relation between coercions of `Lp` subtraction.
    have hxsub' :
        ((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x =
          ((translateL2 (μ := (volume : Measure E)) (-t)) F) x - F x := by
      simpa using hxsub
    -- Rewrite to the desired expression using the two pointwise identities.
    rw [hxsub', hx1, hx2]
  have hcalc :
      ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 =
        ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E) := by
    have h1 :=
      norm_sq_eq_integral_sq (E := E) (v := ((translateL2 (μ := (volume : Measure E)) (-t)) F - F))
    have h2 :
        ∫ x, (((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x) ^ 2
            ∂(volume : Measure E) =
          ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E) := by
      refine MeasureTheory.integral_congr_ae ?_
      exact hdiff.pow_const 2
    exact h1.trans h2
  simpa [F, f] using hcalc
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
