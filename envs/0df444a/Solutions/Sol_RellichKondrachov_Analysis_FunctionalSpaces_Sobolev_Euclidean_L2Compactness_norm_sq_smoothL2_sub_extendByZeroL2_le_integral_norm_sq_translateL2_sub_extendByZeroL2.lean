-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.norm_sq_smoothL2_sub_extendByZeroL2_le_integral_norm_sq_translateL2_sub_extendByZeroL2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:41:41.278376+00:00
-- url     : https://prove2.me/submissions/a5a810d4-a190-40f4-a0f2-61fe20182a60

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
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_norm_sq_translateL2_sub_extendByZeroL2_eq_integral_sq
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothFun_sub_extendByZeroFun_sq_le_integral_sq
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_extendByZeroL2_ae_eq
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothL2_ae_eq

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
theorem _root_.solution
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 ≤
      ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) (extendByZeroL2 (E := E) (K := K) hKm u)
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
          ∂kernelMeasure (E := E) ψ := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  have : MeasureTheory.IsProbabilityMeasure μ :=
    isProbabilityMeasure_kernelMeasure (E := E) (ψ := ψ) hψc hψcs hψ0 hψint
  have : MeasureTheory.IsFiniteMeasure μ := by infer_instance
  have : MeasureTheory.SFinite μ := by infer_instance
  let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  let S : (E →₂[(volume : Measure E)] ℝ) := smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
  have hS_ae :
      (S : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
    smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
  have hF_ae : (F : E → ℝ) =ᵐ[(volume : Measure E)] f :=
    extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
  have hSF_ae :
      (fun x : E => (S - F) x) =ᵐ[(volume : Measure E)] fun x =>
        smoothFun (E := E) (K := K) ψ u x - f x := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub S F, hS_ae, hF_ae] with x hxsub hxS hxF
    have hxsub' : (S - F) x = S x - F x := by
      simpa using hxsub
    rw [hxsub', hxS, hxF]
  have hnorm_sq :
      ‖S - F‖ ^ 2 =
        ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) := by
    have h1 := norm_sq_eq_integral_sq (E := E) (v := (S - F))
    have h2 :
        (∫ x, ((S - F) x) ^ 2 ∂(volume : Measure E)) =
          ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) := by
      refine MeasureTheory.integral_congr_ae ?_
      exact hSF_ae.pow_const 2
    exact h1.trans h2
  have hLHS_int :
      MeasureTheory.Integrable (fun x : E => (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2)
        (volume : Measure E) := by
    have hv_mem : MeasureTheory.MemLp (fun x : E => (S - F : E →₂[(volume : Measure E)] ℝ) x)
        (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp (S - F)
    have hv_int :
        MeasureTheory.Integrable
          (fun x : E => ‖(S - F : E →₂[(volume : Measure E)] ℝ) x‖ ^ (2 : ℕ))
          (volume : Measure E) :=
      MeasureTheory.MemLp.integrable_norm_pow (μ := (volume : Measure E)) (f := fun x =>
        (S - F : E →₂[(volume : Measure E)] ℝ) x) (p := 2) hv_mem (by decide)
    -- Replace `‖·‖^2` by `(_)^2` in `ℝ`, then transport along the AE equality.
    have hv_sq :
        MeasureTheory.Integrable (fun x : E => ((S - F : E →₂[(volume : Measure E)] ℝ) x) ^ 2)
          (volume : Measure E) := by
      simpa [Real.norm_eq_abs, sq_abs] using hv_int
    exact hv_sq.congr (hSF_ae.pow_const 2)
  -- Show integrability on the product measure, so we can use Fubini/Tonelli for the translation
  -- error.
  let h : E × E → ℝ := fun z => (f (z.1 - z.2) - f z.1) ^ 2
  have hf_mem : MeasureTheory.MemLp f (2 : ℝ≥0∞) (volume : Measure E) := by
    -- Again use the AE bridge from the `L²` packaging.
    have hF : MeasureTheory.MemLp (fun x : E => (F : E → ℝ) x) (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp F
    exact (MeasureTheory.memLp_congr_ae hF_ae).1 hF
  have hf_sq_int : MeasureTheory.Integrable (fun x : E => (f x) ^ 2) (volume : Measure E) := by
    have hf_int :
        MeasureTheory.Integrable (fun x : E => ‖f x‖ ^ (2 : ℕ)) (volume : Measure E) :=
      MeasureTheory.MemLp.integrable_norm_pow
        (μ := (volume : Measure E)) (f := f) (p := 2)
        hf_mem (by decide)
    simpa [Real.norm_eq_abs, sq_abs] using hf_int
  have hfst_map :
      MeasureTheory.Integrable (fun x : E => (f x) ^ 2)
        (Measure.map Prod.fst ((volume : Measure E).prod μ)) := by
    simpa [Measure.map_fst_prod] using hf_sq_int
  have hf_fst_sq_prod :
      MeasureTheory.Integrable (fun z : E × E => (f z.1) ^ 2) ((volume : Measure E).prod μ) :=
    (MeasureTheory.Integrable.comp_measurable (μ := (volume : Measure E).prod μ) (f := Prod.fst)
      (g := fun x : E => (f x) ^ 2) hfst_map measurable_fst)
  have hsub :
      MeasureTheory.MeasurePreserving
        (fun z : E × E => (z.1 - z.2, z.2))
        ((volume : Measure E).prod μ)
        ((volume : Measure E).prod μ) :=
    MeasureTheory.measurePreserving_sub_prod (μ := (volume : Measure E)) (ν := μ)
  have hf_shift_sq_prod :
      MeasureTheory.Integrable (fun z : E × E => (f (z.1 - z.2)) ^ 2)
        ((volume : Measure E).prod μ) := by
    have := (hsub.integrable_comp hf_fst_sq_prod.aestronglyMeasurable).2 hf_fst_sq_prod
    exact this
  have hdom :
      MeasureTheory.Integrable (fun z : E × E => (2 : ℝ) * ((f (z.1 - z.2)) ^ 2 + (f z.1) ^ 2))
        ((volume : Measure E).prod μ) := by
    simpa [mul_add, two_mul] using (hf_shift_sq_prod.add hf_fst_sq_prod).const_mul (2 : ℝ)
  have hf_fst_aesm :
      MeasureTheory.AEStronglyMeasurable (fun z : E × E => f z.1)
        ((volume : Measure E).prod μ) := by
    have hf_map :
        MeasureTheory.AEStronglyMeasurable f
          (Measure.map Prod.fst
            ((volume : Measure E).prod μ)) := by
      simpa [Measure.map_fst_prod] using hf_mem.aestronglyMeasurable
    exact MeasureTheory.AEStronglyMeasurable.comp_measurable
      (μ := (volume : Measure E).prod μ) (f := Prod.fst)
      (g := f) hf_map measurable_fst
  have hf_shift_aesm :
      MeasureTheory.AEStronglyMeasurable
        (fun z : E × E => f (z.1 - z.2))
        ((volume : Measure E).prod μ) := by
    have := MeasureTheory.AEStronglyMeasurable.comp_measurePreserving (g := fun z : E × E => f z.1)
      hf_fst_aesm hsub
    exact this
  have h_aesm :
      MeasureTheory.AEStronglyMeasurable h ((volume : Measure E).prod μ) := by
    -- Build up AE-strong measurability from the two components.
    have hsub' :
        MeasureTheory.AEStronglyMeasurable (fun z : E × E => f (z.1 - z.2) - f z.1)
          ((volume : Measure E).prod μ) :=
      hf_shift_aesm.sub hf_fst_aesm
    exact (hsub'.pow 2)
  have hint_h : MeasureTheory.Integrable h ((volume : Measure E).prod μ) := by
    refine MeasureTheory.Integrable.mono (μ := (volume : Measure E).prod μ) hdom h_aesm ?_
    refine Filter.Eventually.of_forall ?_
    rintro ⟨x, t⟩
    have hineq :
        (f (x - t) - f x) ^ 2 ≤ (2 : ℝ) * ((f (x - t)) ^ 2 + (f x) ^ 2) := by
      -- `(a - b)^2 ≤ 2(a^2 + b^2)` as a special case of `add_sq_le`.
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (add_sq_le (a := f (x - t)) (b := -f x))
    have hnonneg : 0 ≤ (f (x - t) - f x) ^ 2 := by nlinarith
    have hsum_nonneg : 0 ≤ (f (x - t)) ^ 2 + (f x) ^ 2 := by nlinarith
    simpa [h, Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_mul,
      abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num),
      abs_of_nonneg hsum_nonneg] using hineq
  have hRHS_int :
      MeasureTheory.Integrable
        (fun x : E => ∫ t, (f (x - t) - f x) ^ 2 ∂μ) (volume : Measure E) := by
    simpa [h] using hint_h.integral_prod_left
  have hpoint :
      (fun x : E => (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2)
        ≤ᶠ[MeasureTheory.ae (volume : Measure E)]
        fun x : E => ∫ t, (f (x - t) - f x) ^ 2 ∂μ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simpa [f, μ] using
      (smoothFun_sub_extendByZeroFun_sq_le_integral_sq (E := E) (K := K) (ψ := ψ)
        hψc hψcs hψ0 hψint hKm u x)
  have hinterm :
      ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) ≤
        ∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E) :=
    MeasureTheory.integral_mono_ae hLHS_int hRHS_int hpoint
  -- Swap the order of integration on the right-hand side.
  have hswap :
      (∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E)) =
        ∫ t, (∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) ∂μ := by
    simpa using (MeasureTheory.integral_integral_swap (μ := (volume : Measure E)) (ν := μ)
      (f := fun x t => (f (x - t) - f x) ^ 2) hint_h)
  -- Identify the inner `x` integral with the `L²` translation norm squared.
  have hinner :
      (fun t : E => ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) =
        fun t : E =>
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 := by
    funext t
    -- Use the previously proved integral identity.
    simpa [F, f] using
      (norm_sq_translateL2_sub_extendByZeroL2_eq_integral_sq
        (E := E) (K := K) (hKm := hKm) t u).symm
  have hRHS_rewrite :
      (∫ t, (∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) ∂μ) =
        ∫ t, ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ∂μ := by
    simp [hinner]
  -- Assemble everything.
  have hmain :
      ‖S - F‖ ^ 2 ≤
        ∫ t, ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ∂μ := by
    -- Convert `‖S-F‖²` to an `x`-integral and apply the integral inequality chain.
    have : ‖S - F‖ ^ 2 ≤ ∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E) := by
      simpa [hnorm_sq] using hinterm
    exact this.trans_eq (hswap.trans hRHS_rewrite)
  -- Restore the original statement.
  simpa [S, F, μ] using hmain
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
