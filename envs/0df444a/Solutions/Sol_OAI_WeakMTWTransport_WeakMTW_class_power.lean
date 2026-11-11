-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.class_power
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:37:49.321519+00:00
-- url     : https://prove2.me/submissions/4f2deb08-325e-4b1b-ba1d-91134d876ec7

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A030
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_maximum_family
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_maximum_template_bound
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_switch_to_positive_excess
import Theorems.Thm_OAI_WeakMTWTransport_exists_uniform_cost_upper_taylor
import Theorems.Thm_OAI_WeakMTWTransport_uniform_family_short_mdifferentiable

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ModifiedScalarDerivatives
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport

lemma modifiedScalar_deriv {B:ℝ → ℝ} (hB:ContDiff ℝ ∞ B) (a D b s:ℝ) :
    deriv (fun x=>modifiedScalar a D B (b,x)) s=1+b/D*deriv B ((s-a)/D) := by
  have H:= (hasDerivAt_id s).add (((hB.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) ((s-a)/D)).hasDerivAt.comp s
    (((hasDerivAt_id s).sub_const a).div_const D)).const_mul b)
  convert! H.deriv using 1
  all_goals try with_reducible_and_instances rfl
  ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MetricDefinitions
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

variable {M : Type*} [MetricSpace M]

variable [CompactSpace M] [Nonempty M]

lemma dualPair_contact_left {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) : ∃ y, contactGap u v x y = 0 := by
  rw [huv.1]
  exact cTransform_gap_zero hv x

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_MiddleExclusion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory
open scoped Topology Interval ContDiff

lemma templateEps_eq : templateEps=1/1024 := by norm_num [templateEps]
lemma centerGamma_pos : 0 < centerGamma := by
  unfold centerGamma
  positivity

lemma centerTemplate_smooth : ContDiff ℝ ∞ centerTemplate := by
  unfold centerTemplate
  have hden : ∀ s:ℝ,1+Real.exp (-centerGamma*(s-5/8))≠0 :=
    fun s => ne_of_gt (by positivity)
  exact contDiff_const.sub (contDiff_const.div (contDiff_const.add
    (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.sub contDiff_const)))) hden)

lemma centerTemplate_bounds (s : ℝ) : -1 < centerTemplate s ∧ centerTemplate s < 1 := by
  have hp := Real.exp_pos (-centerGamma*(s-5/8))
  have hden : 0 < 1+Real.exp (-centerGamma*(s-5/8)) := by positivity
  unfold centerTemplate
  constructor
  · have H : 2/(1+Real.exp (-centerGamma*(s-5/8))) < 2 :=
      (div_lt_iff₀ hden).mpr (by linarith)
    linarith
  · have H : 0 < 2/(1+Real.exp (-centerGamma*(s-5/8))) := by positivity
    linarith

lemma centerTemplate_left {s:ℝ} (hs : s ≤ 1/2) :
    1-templateEps ≤ centerTemplate s := by
  have Hs : centerGamma/8 ≤ -centerGamma*(s-5/8) := by
    nlinarith [centerGamma_pos]
  have he : Real.exp (centerGamma/8)=2047 := by
    rw [centerGamma]
    convert Real.exp_log (by norm_num : (0:ℝ)<2047) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have H := Real.exp_le_exp.mpr Hs
  rw [he] at H
  have hden : 0 < 1+Real.exp (-centerGamma*(s-5/8)) := by positivity
  have HH : 2/(1+Real.exp (-centerGamma*(s-5/8))) ≤ (1:ℝ)/1024 :=
    (div_le_iff₀ hden).mpr (by linarith only [H])
  rw [templateEps_eq]
  unfold centerTemplate
  linarith only [HH]

lemma hasDerivAt_centerTemplate (s:ℝ) :
    HasDerivAt centerTemplate
      (-2*centerGamma*Real.exp (-centerGamma*(s-5/8))/
        (1+Real.exp (-centerGamma*(s-5/8)))^2) s := by
  have he := (((hasDerivAt_id s).sub_const (5/8:ℝ)).const_mul (-centerGamma)).exp
  have H := (hasDerivAt_const s (1:ℝ)).sub ((hasDerivAt_const s (2:ℝ)).div
    ((hasDerivAt_const s (1:ℝ)).add he) (by
      change 1+Real.exp (-centerGamma*(s-5/8))≠0
      exact ne_of_gt (by positivity)))
  have H' : HasDerivAt centerTemplate
      (0-(0*(1+Real.exp (-centerGamma*(s-5/8)))-
        2*(0+Real.exp (-centerGamma*(s-5/8))*(-centerGamma*1)))/
        (1+Real.exp (-centerGamma*(s-5/8)))^2) s := H
  convert H' using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma centerTemplate_deriv_neg (s:ℝ) : deriv centerTemplate s < 0 := by
  rw [(hasDerivAt_centerTemplate s).deriv]
  have hden : 0 < (1+Real.exp (-centerGamma*(s-5/8)))^2 := by positivity
  apply div_neg_of_neg_of_pos _ hden
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) centerGamma_pos)
    (Real.exp_pos _)

lemma outerVelocity_smooth (M0 K eta : ℝ) : ContDiff ℝ ∞ (outerVelocity M0 K eta) := by
  unfold outerVelocity
  fun_prop

lemma outerVelocity_zero_left {M0 K eta s:ℝ} (heta : 0 < eta) (hs : s ≤ -3*eta) :
    outerVelocity M0 K eta s=0 := by
  have H : (s+3*eta)/eta ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) heta.le
  simp only [outerVelocity,Real.smoothTransition.zero_of_nonpos H,mul_zero,zero_mul]

lemma outerVelocity_zero_right {M0 K eta s:ℝ} (hK : 1 ≤ K)
    (hs : 2*(1/(128*(K+1))) ≤ s) : outerVelocity M0 K eta s=0 := by
  have hh : 0 < 1/(128*(K+1)) := by positivity
  have H : 1 ≤ (s-1/(128*(K+1)))/(1/(128*(K+1))) :=
    (le_div_iff₀ hh).mpr (by linarith only [hs])
  simp only [outerVelocity,Real.smoothTransition.one_of_one_le H,sub_self,mul_zero]

lemma outerVelocity_core {M0 K eta s:ℝ} (heta : 0 < eta)
    (hs : -2*eta ≤ s) (hs' : s ≤ 1/(128*(K+1))) (hK : 1 ≤ K) :
    outerVelocity M0 K eta s=128*(M0+3)*(K+1)-(K+1)*s := by
  have hh : 0 < 1/(128*(K+1)) := by positivity
  have Hl : 1 ≤ (s+3*eta)/eta := (le_div_iff₀ heta).mpr (by linarith only [hs])
  have Hr : (s-1/(128*(K+1)))/(1/(128*(K+1))) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith only [hs']) hh.le
  simp only [outerVelocity,Real.smoothTransition.one_of_one_le Hl,
    Real.smoothTransition.zero_of_nonpos Hr,sub_zero,mul_one]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_ExactTemplateCurvature
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport

lemma centerTemplate_deriv_polynomial (s:ℝ) :
    deriv centerTemplate s= -(centerGamma/2)*(1-(centerTemplate s)^2) := by
  rw [(hasDerivAt_centerTemplate s).deriv]
  unfold centerTemplate
  have hd : 1+Real.exp (-centerGamma*(s-5/8)) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

lemma centerTemplate_deriv_bound (s:ℝ) :
    0 < -deriv centerTemplate s ∧ -deriv centerTemplate s ≤ centerGamma/2 := by
  refine ⟨neg_pos.mpr (centerTemplate_deriv_neg s),?_⟩
  rw [centerTemplate_deriv_polynomial]
  nlinarith only [centerGamma_pos,sq_nonneg (centerTemplate s)]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OuterVelocityFactorNonneg
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval ContDiff

namespace WeakMTWTransport

lemma outerVelocity_factor_nonneg {M0 K s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K)
    (hs : s ≤ 2*(1/(128*(K+1)))) :
    0 ≤ 128*(M0+3)*(K+1)-(K+1)*s := by
  have hk : 0 < K+1 := by linarith
  have hu : 2*(1/(128*(K+1))) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hv : s ≤ 128*(M0+3) := le_trans (hs.trans hu) (by linarith)
  have H := mul_nonneg hk.le (sub_nonneg.mpr hv)
  nlinarith only [H]

lemma outerVelocity_nonneg {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) :
    0 ≤ outerVelocity M0 K eta s := by
  by_cases hs : 2*(1/(128*(K+1))) ≤ s
  · rw [outerVelocity_zero_right hK hs]
  · exact mul_nonneg (mul_nonneg (outerVelocity_factor_nonneg hM hK (le_of_not_ge hs))
      (Real.smoothTransition.nonneg _)) (sub_nonneg.mpr (Real.smoothTransition.le_one _))

lemma outerVelocity_le_factor {M0 K eta s:ℝ}
    (hf : 0 ≤ 128*(M0+3)*(K+1)-(K+1)*s) :
    outerVelocity M0 K eta s ≤ 128*(M0+3)*(K+1)-(K+1)*s := by
  have h1 := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one ((s+3*eta)/eta)) hf
  have h2 := mul_le_mul_of_nonneg_left
    (show 1-Real.smoothTransition ((s-1/(128*(K+1)))/(1/(128*(K+1)))) ≤ 1 from by
      linarith only [Real.smoothTransition.nonneg ((s-1/(128*(K+1)))/(1/(128*(K+1))))])
    (mul_nonneg hf (Real.smoothTransition.nonneg ((s+3*eta)/eta)))
  simpa only [mul_one,outerVelocity] using h2.trans (by simpa only [mul_one] using h1)

lemma outerVelocity_le {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta) :
    outerVelocity M0 K eta s ≤ 128*(M0+3)*(K+1)+3*(K+1)*eta := by
  have hk : 0 < K+1 := by linarith
  by_cases hl : s ≤ -3*eta
  · rw [outerVelocity_zero_left heta hl]
    positivity
  by_cases hr : 2*(1/(128*(K+1))) ≤ s
  · rw [outerVelocity_zero_right hK hr]
    positivity
  have H := outerVelocity_le_factor (eta := eta)
    (outerVelocity_factor_nonneg hM hK (le_of_not_ge hr))
  have HH := mul_nonneg hk.le (show 0 ≤ s+3*eta by linarith only [hl])
  nlinarith only [H,HH]

lemma outerVelocity_le_L {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (hs : 0 ≤ s) :
    outerVelocity M0 K eta s ≤ 128*(M0+3)*(K+1) := by
  by_cases hr : 2*(1/(128*(K+1))) ≤ s
  · rw [outerVelocity_zero_right hK hr]
    positivity
  have H := outerVelocity_le_factor (eta := eta)
    (outerVelocity_factor_nonneg hM hK (le_of_not_ge hr))
  have HH := mul_nonneg (show 0 ≤ K+1 by linarith) hs
  linarith only [H,HH]

lemma hasDerivAt_outerPrimitive (M0 K eta s:ℝ) :
    HasDerivAt (outerPrimitive M0 K eta) (outerVelocity M0 K eta s) s := by
  have hc := (outerVelocity_smooth M0 K eta).continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

lemma outerPrimitive_smooth (M0 K eta:ℝ) : ContDiff ℝ ∞ (outerPrimitive M0 K eta) := by
  have hd : deriv (outerPrimitive M0 K eta)=outerVelocity M0 K eta :=
    funext (fun s => (hasDerivAt_outerPrimitive M0 K eta s).deriv)
  have HH : ContDiff ℝ ((∞:ℕ∞ω)+1) (outerPrimitive M0 K eta) := by
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨fun s => (hasDerivAt_outerPrimitive M0 K eta s).differentiableAt,?_,?_⟩
    · simp
    · rw [hd]
      exact outerVelocity_smooth M0 K eta
  simpa using HH

lemma outerTemplate_smooth (M0 K eta:ℝ) : ContDiff ℝ ∞ (outerTemplate M0 K eta) := by
  unfold outerTemplate
  exact (outerPrimitive_smooth M0 K eta).mul (contDiff_const.sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const eta)))

lemma outerPrimitive_monotone {M0 K eta:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) :
    Monotone (outerPrimitive M0 K eta) := by
  apply monotone_of_deriv_nonneg (fun s => (hasDerivAt_outerPrimitive M0 K eta s).differentiableAt)
  intro s
  rw [(hasDerivAt_outerPrimitive M0 K eta s).deriv]
  exact outerVelocity_nonneg hM hK

lemma outerPrimitive_sub (M0 K eta a b:ℝ) :
    outerPrimitive M0 K eta b-outerPrimitive M0 K eta a=
      ∫ q in a..b,outerVelocity M0 K eta q := by
  have hc := (outerVelocity_smooth M0 K eta).continuous
  have H := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 a)
    (hc.intervalIntegrable a b)
  unfold outerPrimitive
  linarith only [H]

lemma outerPrimitive_flat_left {M0 K eta s:ℝ} (heta : 0 < eta) (hs : s ≤ -3*eta) :
    outerPrimitive M0 K eta s=outerPrimitive M0 K eta (-3*eta) := by
  have H := outerPrimitive_sub M0 K eta s (-3*eta)
  have Hz : (∫ q in s..(-3*eta),outerVelocity M0 K eta q)=0 := by
    calc
      _=∫ _q in s..(-3*eta),(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro q hq
        rw [uIcc_of_le hs] at hq
        exact outerVelocity_zero_left heta hq.2
      _=0 := by simp
  linarith only [H,Hz]

lemma outerPrimitive_flat_right {M0 K eta s:ℝ} (hK : 1 ≤ K)
    (hs : 2*(1/(128*(K+1))) ≤ s) :
    outerPrimitive M0 K eta s=outerPrimitive M0 K eta (2*(1/(128*(K+1)))) := by
  have H := outerPrimitive_sub M0 K eta (2*(1/(128*(K+1)))) s
  have Hz : (∫ q in (2*(1/(128*(K+1))))..s,outerVelocity M0 K eta q)=0 := by
    calc
      _=∫ _q in (2*(1/(128*(K+1))))..s,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro q hq
        rw [uIcc_of_le hs] at hq
        exact outerVelocity_zero_right hK hq.1
      _=0 := by simp
  linarith only [H,Hz]

lemma outerPrimitive_bounds {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta)
    (heta1 : eta ≤ 1/128) (hetasmall : eta ≤ templateEps/(24*(128*(M0+3)*(K+1)))) :
    1+templateEps/4 ≤ outerPrimitive M0 K eta s ∧
      outerPrimitive M0 K eta s ≤ 1+templateEps/2+2*(M0+3) := by
  have hk : 0 < K+1 := by linarith
  have hL : 0 < 128*(M0+3)*(K+1) := by positivity
  have hLbig : 3*(K+1)*eta ≤ 128*(M0+3)*(K+1) := by
    have HH := mul_nonneg hk.le (show 0 ≤ 128*(M0+3)-3*eta by linarith only [hM,heta1])
    nlinarith only [HH]
  have he : 6*eta*(128*(M0+3)*(K+1)) ≤ templateEps/4 := by
    have HH := (le_div_iff₀ (show 0 < 24*(128*(M0+3)*(K+1)) by positivity)).mp hetasmall
    nlinarith only [HH]
  have hc := (outerVelocity_smooth M0 K eta).continuous
  have Hleft := intervalIntegral.integral_mono_on (show -3*eta ≤ 0 by linarith)
    (hc.intervalIntegrable (μ := volume) (-3*eta) 0) (continuous_const.intervalIntegrable (-3*eta) 0)
    (fun q _ => outerVelocity_le (s := q) hM hK heta)
  rw [intervalIntegral.integral_const] at Hleft
  simp only [smul_eq_mul] at Hleft
  have Hjleft : 1+templateEps/4 ≤ outerPrimitive M0 K eta (-3*eta) := by
    rw [outerPrimitive,intervalIntegral.integral_symm]
    nlinarith only [Hleft,hLbig,he,heta.le]
  have hh : 0 ≤ 2*(1/(128*(K+1))) := by positivity
  have Hright := intervalIntegral.integral_mono_on hh
    (hc.intervalIntegrable (μ := volume) 0 (2*(1/(128*(K+1)))))
    (continuous_const.intervalIntegrable 0 (2*(1/(128*(K+1)))))
    (fun q hq => outerVelocity_le_L (eta := eta) hM hK hq.1)
  rw [intervalIntegral.integral_const] at Hright
  simp only [sub_zero,smul_eq_mul] at Hright
  have heq : 2*(1/(128*(K+1)))*(128*(M0+3)*(K+1))=2*(M0+3) := by
    field_simp
  rw [heq] at Hright
  have Hjright : outerPrimitive M0 K eta (2*(1/(128*(K+1)))) ≤ 1+templateEps/2+2*(M0+3) := by
    unfold outerPrimitive
    linarith only [Hright]
  constructor
  · by_cases hs : s ≤ -3*eta
    · rwa [outerPrimitive_flat_left heta hs]
    · exact Hjleft.trans (outerPrimitive_monotone (eta := eta) hM hK (le_of_not_ge hs))
  · by_cases hs : 2*(1/(128*(K+1))) ≤ s
    · rwa [outerPrimitive_flat_right hK hs]
    · exact (outerPrimitive_monotone (eta := eta) hM hK (le_of_not_ge hs)).trans Hjright

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ExactScalarBounds
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport

lemma modifiedScalar_slope_bounds {B:ℝ → ℝ} (hB:ContDiff ℝ ∞ B)
    {C D b:ℝ} (hC:0 ≤ C) (hD:0 < D) (hb:0 ≤ b) (hbd:b/D*C ≤ 1/2)
    (hder:∀s,|deriv B s|≤C) (a s:ℝ) :
    (1:ℝ)/2 ≤ deriv (fun x=>modifiedScalar a D B (b,x)) s ∧
    deriv (fun x=>modifiedScalar a D B (b,x)) s ≤ 3/2 := by
  rw [modifiedScalar_deriv hB]
  have H:=abs_le.mp (hder ((s-a)/D))
  have p:=mul_le_mul_of_nonneg_left H.1 (div_nonneg hb hD.le)
  have q:=mul_le_mul H.2 le_rfl (div_nonneg hb hD.le) hC
  constructor <;> nlinarith only [p,q,hbd]

lemma modifiedScalar_strictMono {B:ℝ → ℝ} (hB:ContDiff ℝ ∞ B)
    {C D b:ℝ} (hC:0 ≤ C) (hD:0 < D) (hb:0 ≤ b) (hbd:b/D*C ≤ 1/2)
    (hder:∀s,|deriv B s|≤C) (a:ℝ) :
    StrictMono (fun x=>modifiedScalar a D B (b,x)) := by
  apply strictMono_of_deriv_pos
  intro s
  exact lt_of_lt_of_le (by norm_num) (modifiedScalar_slope_bounds hB hC hD hb hbd hder a s).1

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OuterTemplatePrimitive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval ContDiff

namespace WeakMTWTransport

lemma outerTemplate_eq_primitive {M0 K eta s:ℝ} (heta : 0 < eta) (hs : s ≤ 1-eta) :
    outerTemplate M0 K eta s=outerPrimitive M0 K eta s := by
  have H : (s-(1-eta))/eta ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) heta.le
  simp only [outerTemplate,Real.smoothTransition.zero_of_nonpos H,sub_zero,mul_one]

lemma outerTemplate_zero {M0 K eta s:ℝ} (heta : 0 < eta) (hs : 1 ≤ s) :
    outerTemplate M0 K eta s=0 := by
  have H : 1 ≤ (s-(1-eta))/eta := (le_div_iff₀ heta).mpr (by linarith only [hs])
  simp only [outerTemplate,Real.smoothTransition.one_of_one_le H,sub_self,mul_zero]

lemma outerTemplate_nonneg {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta)
    (heta1 : eta ≤ 1/128) (hetasmall : eta ≤ templateEps/(24*(128*(M0+3)*(K+1)))) :
    0 ≤ outerTemplate M0 K eta s := by
  have H := (outerPrimitive_bounds (s := s) hM hK heta heta1 hetasmall).1
  have hJ : 0 ≤ outerPrimitive M0 K eta s := by rw [templateEps_eq] at H; linarith only [H]
  exact mul_nonneg hJ (sub_nonneg.mpr (Real.smoothTransition.le_one _))

lemma outerTemplate_lower {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta)
    (heta1 : eta ≤ 1/128) (hetasmall : eta ≤ templateEps/(24*(128*(M0+3)*(K+1))))
    (hs : s ≤ 1-eta) : 1 ≤ outerTemplate M0 K eta s := by
  rw [outerTemplate_eq_primitive heta hs]
  have H := (outerPrimitive_bounds (s := s) hM hK heta heta1 hetasmall).1
  rw [templateEps_eq] at H
  linarith only [H]

lemma outerTemplate_upper {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta)
    (heta1 : eta ≤ 1/128) (hetasmall : eta ≤ templateEps/(24*(128*(M0+3)*(K+1)))) :
    outerTemplate M0 K eta s ≤ 2*M0+8 := by
  obtain ⟨H1,H2⟩ := outerPrimitive_bounds (s := s) hM hK heta heta1 hetasmall
  rw [templateEps_eq] at H1 H2
  have hJ : 0 ≤ outerPrimitive M0 K eta s := by linarith only [H1]
  have H := mul_le_mul_of_nonneg_left
    (show 1-Real.smoothTransition ((s-(1-eta))/eta) ≤ 1 by
      linarith only [Real.smoothTransition.nonneg ((s-(1-eta))/eta)]) hJ
  change outerTemplate M0 K eta s ≤ outerPrimitive M0 K eta s*1 at H
  linarith only [H,H2]

lemma outerTemplate_zero_level {M0 K eta:ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1/128) :
    outerTemplate M0 K eta 0=1+templateEps/2 := by
  rw [outerTemplate_eq_primitive heta (by linarith only [heta1])]
  simp [outerPrimitive]

lemma outerPrimitive_core_gain {M0 K eta:ℝ} (hK : 1 ≤ K) (heta : 0 < eta) :
    outerPrimitive M0 K eta (1/(128*(K+1)))-outerPrimitive M0 K eta 0 =
      M0+3-1/(32768*(K+1)) := by
  let h : ℝ := 1/(128*(K+1))
  have hh : 0 ≤ h := by dsimp [h] <;> positivity
  have H : (∫ q in (0:ℝ)..h,outerVelocity M0 K eta q)=
      ∫ q in (0:ℝ)..h,(128*(M0+3)*(K+1)-(K+1)*q) := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le hh] at hq
    exact outerVelocity_core heta (by linarith only [hq.1,heta]) hq.2 hK
  rw [outerPrimitive_sub,H]
  rw [intervalIntegral.integral_sub intervalIntegrable_const (show IntervalIntegrable (fun q : ℝ => (K+1)*q) volume 0 h from
      (show Continuous (fun q : ℝ => (K+1)*q) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
  simp only [sub_zero,zero_pow (by norm_num : 2≠0),smul_eq_mul]
  dsimp [h]
  have hk : K+1≠0 := by linarith only [hK]
  field_simp
  ring

lemma outerTemplate_barrier {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta)
    (heta1 : eta ≤ 1/128) (hs : 1/16 ≤ s) (hs' : s ≤ 1-eta) :
    outerTemplate M0 K eta 0+1 ≤ outerTemplate M0 K eta s := by
  have hk : 0 < K+1 := by linarith only [hK]
  have hh : 1/(128*(K+1)) ≤ s := by
    have H : 1/(128*(K+1)) ≤ 1/16 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hK])
    exact H.trans hs
  have hcorr : 1/(32768*(K+1)) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hK])
  have H := outerPrimitive_core_gain (M0 := M0) hK heta
  have Hm := outerPrimitive_monotone (eta := eta) hM hK hh
  rw [outerTemplate_eq_primitive heta hs',outerTemplate_eq_primitive heta (by linarith only [heta1])]
  linarith only [H,Hm,hcorr,hM]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_OuterDerivativeBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma exists_outerTemplate_deriv_bound {M0 K eta:ℝ} (heta:0 < eta) (heta1:eta ≤ 1/128) :
    ∃C:ℝ,0 ≤ C ∧ ∀s,|deriv (outerTemplate M0 K eta) s| ≤ C := by
  have hc:Continuous (deriv (outerTemplate M0 K eta)) :=
    (outerTemplate_smooth M0 K eta).continuous_deriv (by simp)
  obtain ⟨C,hC⟩:= (isCompact_Icc : IsCompact (Icc (-1) (2:ℝ))).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro s
  by_cases hs:s∈Icc (-1) (2:ℝ)
  · exact (hC s hs).trans (le_max_left _ _)
  have hd:deriv (outerTemplate M0 K eta) s=0 := by
    have hh:s < -1 ∨ 2 < s := by simpa only [mem_Icc,not_and_or,not_le] using hs
    rcases hh with h | h
    · have he:outerTemplate M0 K eta =ᶠ[𝓝 s] outerPrimitive M0 K eta := by
        filter_upwards [eventually_lt_nhds (show s<1-eta by linarith only [h,heta1])] with t ht
        exact outerTemplate_eq_primitive heta ht.le
      rw [he.deriv_eq,(hasDerivAt_outerPrimitive M0 K eta s).deriv]
      exact outerVelocity_zero_left heta (by linarith only [h,heta1])
    · have he:outerTemplate M0 K eta =ᶠ[𝓝 s] (fun _=>0) := by
        filter_upwards [eventually_gt_nhds (show 1 < s by linarith only [h])] with t ht
        exact outerTemplate_zero heta ht.le
      rw [he.deriv_eq,deriv_const]
  rw [hd,abs_zero]
  exact le_max_right _ _

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarFamilyBounds
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter
open scoped ContDiff Topology NNReal

namespace WeakMTWTransport

lemma modifiedScalar_lipschitz {B:ℝ → ℝ} (hB:ContDiff ℝ ∞ B)
    {C D b:ℝ} (hC:0 ≤ C) (hD:0 < D) (hb:0 ≤ b) (hbd:b/D*C ≤ 1/2)
    (hder:∀s,|deriv B s|≤C) (a:ℝ) :
    LipschitzWith 2 (fun s=>modifiedScalar a D B (b,s)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact fun s=>(scalar_family_derivable (modifiedScalar_contDiff hB a D) (b,s)).differentiableAt
  · intro s
    apply (NNReal.coe_le_coe).mp
    rw [coe_nnnorm,Real.norm_eq_abs]
    obtain ⟨hl,hu⟩:=modifiedScalar_slope_bounds hB hC hD hb hbd hder a s
    rw [abs_of_nonneg (by linarith only [hl])]
    norm_num only [NNReal.coe_ofNat]
    linarith only [hu]

lemma exact_center_deriv_abs (s:ℝ) : |deriv centerTemplate s| ≤ centerGamma/2 := by
  rw [abs_of_neg (centerTemplate_deriv_neg s)]
  exact (centerTemplate_deriv_bound s).2

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_GlobalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.active_hull_global_support
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x)) :
    p ∈ minimizingVectors x ∧ ∀ a : M,
      cTransform v x+cost x (riemannianExp x p) ≤
        cTransform v a+cost a (riemannianExp x p) :=
  hmtw.global_support hv (active_hull_subset_normalSubdifferential hv x hp)

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

omit [CompactSpace M] [Nonempty M] in
lemma continuous_twoMountain (x y₀ y₁ : M) : Continuous (twoMountain x y₀ y₁) :=
  (continuous_const.sub (continuous_cost_left y₀)).max (continuous_const.sub (continuous_cost_left y₁))

omit [CompactSpace M] [Nonempty M] in
lemma twoMountain_self (x y₀ y₁ : M) : twoMountain x y₀ y₁ x=0 := by simp [twoMountain]

lemma cTransform_eq_of_lower_mountain {f : M → ℝ} (hf : Continuous f)
    {x y : M} (hx : f x=0) (hm : ∀ z, cost x y-cost z y≤f z) :
    cTransform f y = -cost x y := by
  apply le_antisymm
  · rw [cTransform_le_iff hf]
    intro z
    rw [cost_symm y z]
    linarith [hm z]
  · have hh := cTransform_gap_nonneg hf y x
    rw [contactGap,cost_symm y x,hx] at hh
    linarith

lemma cTransform_twoMountain_left (x y₀ y₁ : M) :
    cTransform (twoMountain x y₀ y₁) y₀ = -cost x y₀ :=
  cTransform_eq_of_lower_mountain (continuous_twoMountain x y₀ y₁)
    (twoMountain_self x y₀ y₁) (fun _ => le_max_left _ _)

lemma cTransform_twoMountain_right (x y₀ y₁ : M) :
    cTransform (twoMountain x y₀ y₁) y₁ = -cost x y₁ :=
  cTransform_eq_of_lower_mountain (continuous_twoMountain x y₀ y₁)
    (twoMountain_self x y₀ y₁) (fun _ => le_max_right _ _)

lemma cTransform_cTransform_twoMountain (x y₀ y₁ : M) :
    cTransform (cTransform (twoMountain x y₀ y₁))=twoMountain x y₀ y₁ := by
  funext z
  apply le_antisymm (cTransform_cTransform_le (continuous_twoMountain x y₀ y₁) z)
  apply max_le
  · have h := cTransform_gap_nonneg (continuous_cTransform (continuous_twoMountain x y₀ y₁)) z y₀
    rw [contactGap,cTransform_twoMountain_left] at h
    linarith
  · have h := cTransform_gap_nonneg (continuous_cTransform (continuous_twoMountain x y₀ y₁)) z y₁
    rw [contactGap,cTransform_twoMountain_right] at h
    linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SectionOscillation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

section SectionOscillation
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

omit [Nonempty M] in
lemma isCompact_gapSection {u v : M → ℝ} (hv : Continuous v) (x : M) (r : ℝ) :
    IsCompact (gapSection u v x r) := by
  apply IsClosed.isCompact
  exact isClosed_le ((continuous_const.add (continuous_cost_right x)).add hv) continuous_const

lemma gapSection_nonempty {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    (gapSection u v x r).Nonempty := by
  obtain ⟨y, hy⟩ := dualPair_contact_left hv huv x
  exact ⟨y, by simpa only [gapSection, mem_ofPred_eq, hy] using hr⟩

lemma sectionOscillation_extrema {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    ∃ y0 ∈ gapSection u v x r, ∃ y1 ∈ gapSection u v x r,
      (∀ y ∈ gapSection u v x r, v y0 ≤ v y) ∧
      (∀ y ∈ gapSection u v x r, v y ≤ v y1) ∧
      sectionOscillation u v x r = v y1 - v y0 := by
  have hc := isCompact_gapSection (u := u) hv x r
  have hn := gapSection_nonempty hv huv x hr
  obtain ⟨y0, hy0, hmin⟩ := hc.exists_isMinOn hn hv.continuousOn
  obtain ⟨y1, hy1, hmax⟩ := hc.exists_isMaxOn hn hv.continuousOn
  have hleast : IsLeast (v '' gapSection u v x r) (v y0) := by
    refine ⟨mem_image_of_mem v hy0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmin hy
  have hgreatest : IsGreatest (v '' gapSection u v x r) (v y1) := by
    refine ⟨mem_image_of_mem v hy1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  exact ⟨y0, hy0, y1, hy1, fun _ hy => hmin hy, fun _ hy => hmax hy,
    by rw [sectionOscillation, hleast.csInf_eq, hgreatest.csSup_eq]⟩

lemma sectionOscillation_nonneg {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ sectionOscillation u v x r := by
  obtain ⟨y0, _, y1, hy1, hmin, _, heq⟩ := sectionOscillation_extrema hv huv x hr
  rw [heq]
  exact sub_nonneg.mpr (hmin y1 hy1)

lemma sectionOscillation_mono {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    sectionOscillation u v x r ≤ sectionOscillation u v x R := by
  obtain ⟨y0, hy0, y1, hy1, _, _, heq⟩ := sectionOscillation_extrema hv huv x hr
  obtain ⟨z0, _, z1, _, hmin, hmax, heq'⟩ :=
    sectionOscillation_extrema hv huv x (hr.trans hrR)
  have h0 := hmin y0 (hy0.trans hrR)
  have h1 := hmax y1 (hy1.trans hrR)
  rw [heq, heq']
  linarith

lemma sectionOscillation_le_diam_sq {u v : M → ℝ} (hu : Continuous u)
    (hv : Continuous v) (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    sectionOscillation u v x r ≤ Metric.diam (univ : Set M) ^ 2 := by
  let D : ℝ≥0 := ⟨Metric.diam (univ : Set M), Metric.diam_nonneg⟩
  have hD (x y : M) : dist x y ≤ D :=
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  have hLip : LipschitzWith D v := by
    rw [huv.2]
    exact cTransform_lipschitz hu hD
  obtain ⟨y0, _, y1, _, _, _, heq⟩ := sectionOscillation_extrema hv huv x hr
  have hh := hLip.dist_le_mul y1 y0
  rw [Real.dist_eq] at hh
  rw [heq]
  calc
    v y1 - v y0 ≤ |v y1 - v y0| := le_abs_self _
    _ ≤ (D : ℝ) * dist y1 y0 := hh
    _ ≤ (D : ℝ) ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left (hD y1 y0) D.coe_nonneg]

variable [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
lemma densityDualClass_isDual {vol : Measure M} {lam cap : ℝ} {x0 : M}
    {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)} (h : uv ∈ densityDualClass vol lam cap x0) :
    IsCostDualPair uv.1 uv.2 := by
  constructor
  · exact congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.1.2.1.symm
  · exact congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.1.2.2.symm

omit [BorelSpace M] in
lemma classSectionOscillations_nonempty {vol : Measure M} {lam cap : ℝ} {x0 : M}
    (hc : (densityDualClass vol lam cap x0).Nonempty) (r : ℝ) :
    (classSectionOscillations vol lam cap x0 r).Nonempty := by
  obtain ⟨uv, huv⟩ := hc
  exact ⟨_, uv, huv, x0, rfl⟩

omit [BorelSpace M] in
lemma classSectionOscillations_bddAbove {vol : Measure M} {lam cap : ℝ} {x0 : M}
    {r : ℝ} (hr : 0 ≤ r) : BddAbove (classSectionOscillations vol lam cap x0 r) := by
  refine ⟨Metric.diam (univ : Set M) ^ 2, ?_⟩
  rintro _ ⟨uv, huv, x, rfl⟩
  exact sectionOscillation_le_diam_sq uv.1.continuous uv.2.continuous
    (densityDualClass_isDual huv) x hr

omit [BorelSpace M] in
lemma sectionOscillation_le_classOscillation {vol : Measure M} {lam cap : ℝ} {x0 : M}
    {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)} (huv : uv ∈ densityDualClass vol lam cap x0)
    (x : M) {r : ℝ} (hr : 0 ≤ r) :
    sectionOscillation uv.1 uv.2 x r ≤ classOscillation vol lam cap x0 r := by
  exact le_csSup (classSectionOscillations_bddAbove hr) ⟨uv, huv, x, rfl⟩

omit [BorelSpace M] in
lemma classOscillation_bounds {vol : Measure M} {lam cap : ℝ} {x0 : M}
    (hc : (densityDualClass vol lam cap x0).Nonempty) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ classOscillation vol lam cap x0 r ∧
      classOscillation vol lam cap x0 r ≤ Metric.diam (univ : Set M) ^ 2 := by
  constructor
  · obtain ⟨uv, huv⟩ := hc
    exact (sectionOscillation_nonneg uv.2.continuous (densityDualClass_isDual huv) x0 hr).trans
      (sectionOscillation_le_classOscillation huv x0 hr)
  · apply csSup_le (classSectionOscillations_nonempty hc r)
    rintro _ ⟨uv, huv, x, rfl⟩
    exact sectionOscillation_le_diam_sq uv.1.continuous uv.2.continuous
      (densityDualClass_isDual huv) x hr

omit [BorelSpace M] in
lemma classOscillation_monotone {vol : Measure M} {lam cap : ℝ} {x0 : M}
    (hc : (densityDualClass vol lam cap x0).Nonempty) :
    MonotoneOn (classOscillation vol lam cap x0) (Ici 0) := by
  intro r hr R hR hrR
  apply csSup_le (classSectionOscillations_nonempty hc r)
  rintro _ ⟨uv, huv, x, rfl⟩
  exact (sectionOscillation_mono uv.2.continuous (densityDualClass_isDual huv) x hr hrR).trans
    (sectionOscillation_le_classOscillation huv x hR)

omit [BorelSpace M] in

lemma exists_section_with_large_oscillation {vol : Measure M} {lam cap : ℝ} {x0 : M}
    (hc : (densityDualClass vol lam cap x0).Nonempty) {r q : ℝ}
    (hr : 0 ≤ r) (hq : q < classOscillation vol lam cap x0 r) :
    ∃ uv ∈ densityDualClass vol lam cap x0, ∃ x y0 y1 : M,
      y0 ∈ gapSection uv.1 uv.2 x r ∧ y1 ∈ gapSection uv.1 uv.2 x r ∧
      (∀ y ∈ gapSection uv.1 uv.2 x r, uv.2 y0 ≤ uv.2 y) ∧
      (∀ y ∈ gapSection uv.1 uv.2 x r, uv.2 y ≤ uv.2 y1) ∧
      sectionOscillation uv.1 uv.2 x r = uv.2 y1 - uv.2 y0 ∧
      q < uv.2 y1 - uv.2 y0 := by
  obtain ⟨a, ⟨uv, huv, x, rfl⟩, ha⟩ := exists_lt_of_lt_csSup
    (classSectionOscillations_nonempty hc r) hq
  obtain ⟨y0, hy0, y1, hy1, hmin, hmax, heq⟩ :=
    sectionOscillation_extrema uv.2.continuous (densityDualClass_isDual huv) x hr
  exact ⟨uv, huv, x, y0, y1, hy0, hy1, hmin, hmax, heq, heq ▸ ha⟩

end SectionOscillation

open Filter

lemma exists_small_step (f : ℝ → ℝ) (a h q : ℝ) {m : ℕ} (hm : 0 < m)
    (hbound : f (a + m * h) - f a ≤ m * q) :
    ∃ i : ℕ, i < m ∧ f (a + (i + 1) * h) - f (a + i * h) ≤ q := by
  have hsum : (∑ i ∈ Finset.range m, (f (a + (i + 1) * h) - f (a + i * h))) ≤
      ∑ _i ∈ Finset.range m, q := by
    have ht := Finset.sum_range_sub (fun i : ℕ => f (a + i * h)) m
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] at ht
    rw [ht]
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hbound
  obtain ⟨i, hi, hb⟩ := Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.mpr hm⟩ hsum
  exact ⟨i, Finset.mem_range.mp hi, hb⟩

lemma logarithmic_plateau_quantitative {f : ℝ → ℝ} (hmono : Monotone f)
    (hzero : ∀ s, 0 ≤ f s)
    (hsub : ∀ eps : ℝ, 0 < eps → ∀ L : ℝ, ∃ N : ℝ, L ≤ N ∧ f N ≤ eps * N)
    {J : ℝ} (hJ : 1 ≤ J) :
    ∃ A B : ℝ, J ^ 2 ≤ A ∧ B = A + J ∧
      f B - f A ≤ J⁻¹ ∧ f B ≤ A / J ^ 2 := by
  have hJ0 : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have hden : 0 < 4 * J ^ 2 := by positivity
  obtain ⟨N, hN, hfN⟩ := hsub (4 * J ^ 2)⁻¹ (inv_pos.mpr hden) (4 * J ^ 2)
  have hN0 : 0 ≤ N := (le_of_lt hden).trans hN
  let m : ℕ := ⌊N / (2 * J)⌋₊
  have hmle : (m : ℝ) ≤ N / (2 * J) := Nat.floor_le (by positivity)
  have hmlt : N / (2 * J) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmle' : 2 * J * m ≤ N := by
    have hh := (le_div_iff₀ (show 0 < 2 * J by positivity)).mp hmle
    nlinarith
  have hmlt' : N < 2 * J * (m + 1) := by
    have hh := (div_lt_iff₀ (show 0 < 2 * J by positivity)).mp hmlt
    nlinarith
  have hmJ : J ≤ (m : ℝ) := by nlinarith
  have hm1 : (1 : ℝ) ≤ m := hJ.trans hmJ
  have hmpos : 0 < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm1)
  have hNupper : N ≤ 4 * J * m := by nlinarith
  have hfNm : f N ≤ (m : ℝ) / J := by
    have hh : f N * (4 * J ^ 2) ≤ N := by
      calc
        f N * (4 * J ^ 2) ≤ ((4 * J ^ 2)⁻¹ * N) * (4 * J ^ 2) :=
          mul_le_mul_of_nonneg_right hfN hden.le
        _ = N := by field_simp
    apply (le_div_iff₀ hJ0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hNupper) (show 0 ≤ J by positivity)]
  have hsum : f (J * m + (m : ℝ) * J) - f (J * m) ≤ (m : ℝ) * J⁻¹ := by
    have htop := hmono (show J * m + (m : ℝ) * J ≤ N by nlinarith)
    have hbot := hzero (J * m)
    rw [div_eq_mul_inv] at hfNm
    linarith
  obtain ⟨i, hi, hstep⟩ := exists_small_step f (J * m) J J⁻¹ hmpos hsum
  let A := J * m + (i : ℝ) * J
  let B := J * m + ((i : ℝ) + 1) * J
  have hA : J ^ 2 ≤ A := by
    dsimp [A]
    nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have hB : B ≤ N := by
    have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
    dsimp [B]
    nlinarith
  refine ⟨A, B, hA, by dsimp [A, B] <;> ring, hstep, ?_⟩
  calc
    f B ≤ f N := hmono hB
    _ ≤ (m : ℝ) / J := hfNm
    _ ≤ A / J ^ 2 := by
      apply (div_le_div_iff₀ hJ0 (sq_pos_of_pos hJ0)).mpr
      dsimp [A]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) i) (sq_nonneg J)]

lemma log_sublinear_of_no_power {F : ℝ → ℝ} {CF : ℝ} (hCF : 0 < CF)
    (hFpos : ∀ r : ℝ, 0 < r → 0 < F r) (hno : ¬ HasPowerUpperBound F) :
    ∀ eps : ℝ, 0 < eps → ∀ L : ℝ, ∃ N : ℝ, L ≤ N ∧
      Real.log (CF / F (Real.exp (-N))) ≤ eps * N := by
  intro eps heps L
  have hbad : ∃ r : ℝ, 0 < r ∧ r < Real.exp (-L) ∧ CF * r ^ eps < F r := by
    by_contra! hgood
    exact hno ⟨eps, CF, Real.exp (-L), heps, hCF, Real.exp_pos _,
      fun r hr hr0 => hgood r hr hr0⟩
  obtain ⟨r, hr, hr0, hbad⟩ := hbad
  refine ⟨-Real.log r, ?_, ?_⟩
  · have hh := Real.log_lt_log hr hr0
    rw [Real.log_exp] at hh
    linarith
  · have hh := Real.log_lt_log (mul_pos hCF (Real.rpow_pos_of_pos hr eps)) hbad
    rw [Real.log_mul hCF.ne' (Real.rpow_pos_of_pos hr eps).ne', Real.log_rpow hr] at hh
    rw [neg_neg, Real.exp_log hr, Real.log_div hCF.ne' (hFpos r hr).ne']
    linarith

lemma logarithmic_profile_nonneg {F : ℝ → ℝ} {CF : ℝ}
    (hFpos : ∀ r : ℝ, 0 < r → 0 < F r)
    (hbound : ∀ r : ℝ, 0 < r → F r ≤ CF) (s : ℝ) :
    0 ≤ Real.log (CF / F (Real.exp (-s))) := by
  apply Real.log_nonneg
  exact (one_le_div (hFpos _ (Real.exp_pos _))).mpr (hbound _ (Real.exp_pos _))

lemma logarithmic_profile_monotone {F : ℝ → ℝ} {CF : ℝ} (hCF : 0 < CF)
    (hFpos : ∀ r : ℝ, 0 < r → 0 < F r) (hmono : MonotoneOn F (Ioi 0)) :
    Monotone (fun s : ℝ => Real.log (CF / F (Real.exp (-s)))) := by
  intro a b hab
  apply Real.log_le_log (div_pos hCF (hFpos _ (Real.exp_pos _)))
  exact div_le_div_of_nonneg_left hCF.le (hFpos _ (Real.exp_pos _))
    (hmono (Real.exp_pos _) (Real.exp_pos _) (Real.exp_le_exp.mpr (neg_le_neg hab)))

lemma no_power_logarithmic_plateau {F : ℝ → ℝ} {CF : ℝ} (hCF : 0 < CF)
    (hFpos : ∀ r : ℝ, 0 < r → 0 < F r)
    (hbound : ∀ r : ℝ, 0 < r → F r ≤ CF) (hmono : MonotoneOn F (Ioi 0))
    (hno : ¬ HasPowerUpperBound F) {J : ℝ} (hJ : 1 ≤ J) :
    ∃ A B : ℝ, J ^ 2 ≤ A ∧ B = A + J ∧
      Real.log (CF / F (Real.exp (-B))) - Real.log (CF / F (Real.exp (-A))) ≤ J⁻¹ ∧
      Real.log (CF / F (Real.exp (-B))) ≤ A / J ^ 2 := by
  exact logarithmic_plateau_quantitative
    (logarithmic_profile_monotone hCF hFpos hmono)
    (logarithmic_profile_nonneg hFpos hbound)
    (log_sublinear_of_no_power hCF hFpos hno) hJ

lemma positive_of_no_power {F : ℝ → ℝ} (hmono : MonotoneOn F (Ioi 0))
    (hno : ¬ HasPowerUpperBound F) {r : ℝ} (hr : 0 < r) : 0 < F r := by
  by_contra! hF
  apply hno
  refine ⟨1, 1, r, by norm_num, by norm_num, hr, ?_⟩
  intro t ht htr
  have hh := hmono ht hr htr.le
  simpa only [Real.rpow_one, one_mul] using hh.trans (hF.trans ht.le)

lemma no_power_gap_scale_plateau {F : ℝ → ℝ} {CF : ℝ} (hCF : 0 < CF)
    (hbound : ∀ r : ℝ, 0 < r → F r ≤ CF) (hmono : MonotoneOn F (Ioi 0))
    (hno : ¬ HasPowerUpperBound F) {J : ℝ} (hJ : 1 ≤ J) :
    ∃ A : ℝ, J ^ 2 ≤ A ∧
      F (Real.exp (-A)) ≤ Real.exp J⁻¹ * F (Real.exp (-(A + J))) ∧
      |Real.log (F (Real.exp (-(A + J))))| ≤ |Real.log CF| + A / J ^ 2 := by
  have hpos : ∀ r : ℝ, 0 < r → 0 < F r := fun _ hr => positive_of_no_power hmono hno hr
  obtain ⟨A, B, hA, rfl, hinc, hval⟩ :=
    no_power_logarithmic_plateau hCF hpos hbound hmono hno hJ
  have hpA := hpos (Real.exp (-A)) (Real.exp_pos _)
  have hpB := hpos (Real.exp (-(A+J))) (Real.exp_pos _)
  have hfnonneg := logarithmic_profile_nonneg hpos hbound (A + J)
  rw [Real.log_div hCF.ne' hpB.ne', Real.log_div hCF.ne' hpA.ne'] at hinc
  rw [Real.log_div hCF.ne' hpB.ne'] at hval hfnonneg
  refine ⟨A, hA, ?_, ?_⟩
  · have hlog : Real.log (F (Real.exp (-A))) ≤ J⁻¹ + Real.log (F (Real.exp (-(A+J)))) := by
      linarith
    have hh := Real.exp_le_exp.mpr hlog
    simpa only [Real.exp_add, Real.exp_log hpA, Real.exp_log hpB] using hh
  · calc
      |Real.log (F (Real.exp (-(A+J))))| =
          |Real.log CF - (Real.log CF - Real.log (F (Real.exp (-(A+J)))))| := by ring_nf
      _ ≤ |Real.log CF| + |Real.log CF - Real.log (F (Real.exp (-(A+J))))| := abs_sub _ _
      _ ≤ |Real.log CF| + A / J ^ 2 := by rw [abs_of_nonneg hfnonneg]; linarith

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_DoubleMountain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma minimizingVector_active_twoMountain_left {x : M}
    {p₀ p₁ : TangentSpace 𝓘(ℝ,Model n) x} (hp₀ : p₀∈minimizingVectors x) :
    p₀∈activeLogs (cTransform (twoMountain x (riemannianExp x p₀) (riemannianExp x p₁))) x := by
  refine ⟨hp₀,?_⟩
  rw [contactGap,cTransform_cTransform_twoMountain,twoMountain_self,cTransform_twoMountain_left]
  ring

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma minimizingVector_active_twoMountain_right {x : M}
    {p₀ p₁ : TangentSpace 𝓘(ℝ,Model n) x} (hp₁ : p₁∈minimizingVectors x) :
    p₁∈activeLogs (cTransform (twoMountain x (riemannianExp x p₀) (riemannianExp x p₁))) x := by
  refine ⟨hp₁,?_⟩
  rw [contactGap,cTransform_cTransform_twoMountain,twoMountain_self,cTransform_twoMountain_right]
  ring

lemma WeakMTW.double_mountain (hmtw : WeakMTW (n := n) (M := M)) {x : M}
    {p₀ p₁ : TangentSpace 𝓘(ℝ,Model n) x}
    (hp₀ : p₀∈minimizingVectors x) (hp₁ : p₁∈minimizingVectors x)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    a • p₀+b • p₁∈minimizingVectors x ∧ ∀ z : M,
      cost x (riemannianExp x (a • p₀+b • p₁))-cost z (riemannianExp x (a • p₀+b • p₁)) ≤
        max (cost x (riemannianExp x p₀)-cost z (riemannianExp x p₀))
          (cost x (riemannianExp x p₁)-cost z (riemannianExp x p₁)) := by
  let f := twoMountain x (riemannianExp x p₀) (riemannianExp x p₁)
  have hp : a • p₀+b • p₁∈convexHull ℝ (activeLogs (n := n) (cTransform f) x) :=
    (convex_convexHull _ _)
      (subset_convexHull _ _ (minimizingVector_active_twoMountain_left hp₀))
      (subset_convexHull _ _ (minimizingVector_active_twoMountain_right hp₁)) ha hb hab
  obtain ⟨hmin,hsup⟩ := hmtw.active_hull_global_support
    (continuous_cTransform (continuous_twoMountain x _ _)) hp
  refine ⟨hmin,?_⟩
  intro z
  have hh := hsup z
  rw [cTransform_cTransform_twoMountain,twoMountain_self] at hh
  change 0+cost x (riemannianExp x (a • p₀+b • p₁))≤
    twoMountain x (riemannianExp x p₀) (riemannianExp x p₁) z+
      cost z (riemannianExp x (a • p₀+b • p₁)) at hh
  exact sub_le_iff_le_add.mpr (by simpa only [zero_add,twoMountain] using hh)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_LiftedSections
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma cost_minimizingVector {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) : cost x (riemannianExp x p)=‖p‖^2/2 := by
  unfold cost
  rw [show dist x (riemannianExp x p)=‖p‖ from hp]

lemma mem_liftedGapSection_iff {u v : M → ℝ} {x : M} {r : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} :
    p∈liftedGapSection u v x r ↔ p∈minimizingVectors x ∧ riemannianExp x p∈gapSection u v x r := by
  constructor
  · intro hp
    exact ⟨hp.1,by simpa only [gapSection,mem_ofPred_eq,contactGap,cost_minimizingVector hp.1] using hp.2⟩
  · intro hp
    exact ⟨hp.1,by simpa only [gapSection,mem_ofPred_eq,contactGap,cost_minimizingVector hp.1] using hp.2⟩

variable [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

variable [Nonempty M]

lemma WeakMTW.convex_liftedGapSection (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (huv : IsCostDualPair u v)
    (x : M) (r : ℝ) : Convex ℝ (liftedGapSection (n := n) u v x r) := by
  intro p hp q hq a b ha hb hab
  have hp' := mem_liftedGapSection_iff.mp hp
  have hq' := mem_liftedGapSection_iff.mp hq
  obtain ⟨hm,hcomp⟩ := hmtw.double_mountain hp.1 hq.1 ha hb hab
  rw [mem_liftedGapSection_iff]
  refine ⟨hm,?_⟩
  change u x+cost x (riemannianExp x (a • p+b • q))+v (riemannianExp x (a • p+b • q)) ≤ r
  have HB : cTransform u (riemannianExp x (a • p+b • q))≤
      r-u x-cost x (riemannianExp x (a • p+b • q)) := by
    rw [cTransform_le_iff hu]
    intro z
    rw [cost_symm (riemannianExp x (a • p+b • q)) z]
    have hcp := dualPair_gap_nonneg hv huv z (riemannianExp x p)
    have hcq := dualPair_gap_nonneg hv huv z (riemannianExp x q)
    have hpS : u x+cost x (riemannianExp x p)+v (riemannianExp x p) ≤ r := hp'.2
    have hqS : u x+cost x (riemannianExp x q)+v (riemannianExp x q) ≤ r := hq'.2
    have hpB : cost x (riemannianExp x p)-cost z (riemannianExp x p) ≤ r-u x+u z := by
      dsimp [contactGap] at hcp
      linarith [hpS]
    have hqB : cost x (riemannianExp x q)-cost z (riemannianExp x q) ≤ r-u x+u z := by
      dsimp [contactGap] at hcq
      linarith [hqS]
    have hmax := (hcomp z).trans (max_le hpB hqB)
    linarith
  rw [huv.2]
  linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_SectionDiameter
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section SectionDiameter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.liftedGapSection_diameter_sq (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (huv : IsCostDualPair u v)
    {x : M} {r : ℝ} (hr : 0 ≤ r) {p q : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈liftedGapSection u v x r) (hq : q∈liftedGapSection u v x r) :
    ‖p-q‖^2≤8*(r+sectionOscillation u v x r) := by
  let m := (1/2:ℝ) • p+(1/2:ℝ) • q
  have hm : m∈liftedGapSection u v x r :=
    (hmtw.convex_liftedGapSection hu hv huv x r) hp hq (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨y₀,_,y₁,_,hmin,hmax,heq⟩ := sectionOscillation_extrema hv huv x hr
  have hpS := (mem_liftedGapSection_iff.mp hp).2
  have hqS := (mem_liftedGapSection_iff.mp hq).2
  have hmS := (mem_liftedGapSection_iff.mp hm).2
  have hpl := hmin _ hpS
  have hql := hmin _ hqS
  have hmu := hmax _ hmS
  have hpm := hp.2
  have hqm := hq.2
  have hmn := dualPair_gap_nonneg hv huv x (riemannianExp x m)
  rw [contactGap,cost_minimizingVector hm.1] at hmn
  have norm_m : ‖m‖^2=(‖p‖^2+‖q‖^2)/2-‖p-q‖^2/4 := by
    have hpar := parallelogram_law_with_norm ℝ p q
    dsimp [m]
    rw [←smul_add,norm_smul]
    norm_num
    nlinarith [hpar]
  rw [heq]
  nlinarith [norm_m]

end SectionDiameter
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ModifiedData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
section ModifiedData
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma modified_double_bounds {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a D b : ℝ} {B : ℝ → ℝ}
    (hB : Continuous B) (hb : 0 ≤ b) (hbound : ∀ s,0 ≤ B s) (y : M) :
    v y ≤ cTransform (cTransform (modifiedDatum v a D b B)) y ∧
      cTransform (cTransform (modifiedDatum v a D b B)) y ≤ modifiedDatum v a D b B y := by
  have hw := continuous_modifiedDatum hv a D b hB
  have h1 := cTransform_antitone hv hw
    (fun y => le_add_of_nonneg_right (mul_nonneg hb (hbound _)))
  rw [←hdual.1] at h1
  have h2 := cTransform_antitone (continuous_cTransform hw) hu h1 y
  rw [←hdual.2] at h2
  exact ⟨h2,cTransform_cTransform_le hw y⟩

lemma modified_excess_upper {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a D b : ℝ} {Bc Bo : ℝ → ℝ}
    (hBo : Continuous Bo) (hb : 0 ≤ b) (ho : ∀ s,0 ≤ Bo s) (hc : ∀ s,Bc s ≤ 1)
    (y : M) : modifiedExcess v a D b Bc Bo y ≤ b := by
  have H := (modified_double_bounds (a := a) (D := D) hu hv hdual hBo hb ho y).1
  have Hc := mul_le_mul_of_nonneg_left (hc ((v y-a)/D)) hb
  dsimp only [modifiedExcess,modifiedDatum]
  linarith

end ModifiedData
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_RayBenchmark
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section RayBenchmark
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.section_initial_logs (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {x : M} {p q : TangentSpace 𝓘(ℝ,Model n) x} {r a D : ℝ}
    (hr : 0 ≤ r) (hrD : r≤D/5)
    (hp : p∈liftedGapSection u v x r) (hq : q∈liftedGapSection u v x r)
    (ha : v (riemannianExp x p)=a) (ha1 : v (riemannianExp x q)=a+D)
    (hosc : sectionOscillation u v x r≤D) :
    |‖p‖^2-‖q‖^2-2*D|≤2*r ∧ ‖p-q‖^2≤8*(D+r) ∧
      ‖p‖^2-inner ℝ p q≤6*D ∧ D≤‖p‖^2 := by
  have hdiam := (hmtw.liftedGapSection_diameter_sq hu hv hdual hr hp hq).trans
    (mul_le_mul_of_nonneg_left (show r + sectionOscillation u v x r ≤ D + r by linarith only [hosc]) (by norm_num : (0:ℝ)≤8))
  have hp0 := dualPair_gap_nonneg hv hdual x (riemannianExp x p)
  have hq0 := dualPair_gap_nonneg hv hdual x (riemannianExp x q)
  have hp1 := (mem_liftedGapSection_iff.mp hp).2
  have hq1 := (mem_liftedGapSection_iff.mp hq).2
  change contactGap u v x (riemannianExp x p) ≤ r at hp1
  change contactGap u v x (riemannianExp x q) ≤ r at hq1
  rw [contactGap,cost_minimizingVector hp.1,ha] at hp0 hp1
  rw [contactGap,cost_minimizingVector hq.1,ha1] at hq0 hq1
  have hid := norm_sub_sq_real p q
  refine ⟨abs_le.mpr ⟨by linarith only [hp0,hq1],by linarith only [hp1,hq0]⟩,?_,?_,?_⟩
  · linarith only [hdiam]
  · nlinarith only [hid,hdiam,hp1,hq0,hrD]
  · nlinarith only [hp0,hq1,hrD,hr,sq_nonneg ‖q‖]

end RayBenchmark
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_UniformFixedCrossing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
  (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma minimizing_norm_le_diam {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) : ‖p‖ ≤ Metric.diam (univ : Set M) := by
  rw [←hp]
  exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_ActualPlateaus
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction
open Filter

section ActualPlateaus
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in

lemma exists_actual_plateau_section {vol : Measure M} {lam cap : ℝ} {x0 : M}
    (hc : (densityDualClass vol lam cap x0).Nonempty)
    (hno : ¬ HasPowerUpperBound (classOscillation vol lam cap x0))
    {J : ℝ} (hJ : 1 ≤ J) :
    ∃ A : ℝ, ∃ uv ∈ densityDualClass vol lam cap x0, ∃ x y0 y1 : M,
      J ^ 2 ≤ A ∧
      y0 ∈ gapSection uv.1 uv.2 x (Real.exp (-(A + J))) ∧
      y1 ∈ gapSection uv.1 uv.2 x (Real.exp (-(A + J))) ∧
      (∀ y ∈ gapSection uv.1 uv.2 x (Real.exp (-(A + J))), uv.2 y0 ≤ uv.2 y) ∧
      (∀ y ∈ gapSection uv.1 uv.2 x (Real.exp (-(A + J))), uv.2 y ≤ uv.2 y1) ∧
      sectionOscillation uv.1 uv.2 x (Real.exp (-(A + J))) = uv.2 y1 - uv.2 y0 ∧
      0 < uv.2 y1 - uv.2 y0 ∧
      classOscillation vol lam cap x0 (Real.exp (-A)) ≤
        Real.exp (2 / J) * (uv.2 y1 - uv.2 y0) ∧
      |Real.log (uv.2 y1 - uv.2 y0)| ≤
        |Real.log (1 + Metric.diam (univ : Set M) ^ 2)| + A / J ^ 2 + J⁻¹ := by
  let F := classOscillation vol lam cap x0
  let CF : ℝ := 1 + Metric.diam (univ : Set M) ^ 2
  have hCF : 0 < CF := by dsimp [CF] <;> positivity
  have hJ0 : 0 < J := zero_lt_one.trans_le hJ
  have hJi : 0 < J⁻¹ := inv_pos.mpr hJ0
  have hmono : MonotoneOn F (Ioi 0) :=
    (classOscillation_monotone hc).mono Ioi_subset_Ici_self
  have hbound : ∀ r : ℝ, 0 < r → F r ≤ CF := by
    intro r hr
    exact (classOscillation_bounds hc hr.le).2.trans (by dsimp [CF] <;> linarith)
  obtain ⟨A, hA, hplateau, hlog⟩ := no_power_gap_scale_plateau hCF hbound hmono hno hJ
  have hp : 0 < F (Real.exp (-(A + J))) := positive_of_no_power hmono hno (Real.exp_pos _)
  have hq : Real.exp (-J⁻¹) * F (Real.exp (-(A + J))) < F (Real.exp (-(A + J))) := by
    have hh := mul_lt_mul_of_pos_right (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hJi)) hp
    simpa only [one_mul] using hh
  obtain ⟨uv, huv, x, y0, y1, hy0, hy1, hmin, hmax, heq, hlarge⟩ :=
    exists_section_with_large_oscillation hc (Real.exp_pos _).le hq
  have hDpos : 0 < uv.2 y1 - uv.2 y0 := (mul_pos (Real.exp_pos _) hp).trans hlarge
  have hDle : uv.2 y1 - uv.2 y0 ≤ F (Real.exp (-(A + J))) := by
    rw [← heq]
    exact sectionOscillation_le_classOscillation huv x (Real.exp_pos _).le
  refine ⟨A, uv, huv, x, y0, y1, hA, hy0, hy1, hmin, hmax, heq, hDpos, ?_, ?_⟩
  · have hFle : F (Real.exp (-(A + J))) ≤ Real.exp J⁻¹ * (uv.2 y1 - uv.2 y0) := by
      calc
        F (Real.exp (-(A + J))) =
            Real.exp J⁻¹ * (Real.exp (-J⁻¹) * F (Real.exp (-(A + J)))) := by
          rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp J⁻¹ * (uv.2 y1 - uv.2 y0) :=
          mul_le_mul_of_nonneg_left hlarge.le (Real.exp_pos _).le
    calc
      F (Real.exp (-A)) ≤ Real.exp J⁻¹ * F (Real.exp (-(A + J))) := hplateau
      _ ≤ Real.exp J⁻¹ * (Real.exp J⁻¹ * (uv.2 y1 - uv.2 y0)) :=
        mul_le_mul_of_nonneg_left hFle (Real.exp_pos _).le
      _ = Real.exp (2 / J) * (uv.2 y1 - uv.2 y0) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  · have hupper := Real.log_le_log hDpos hDle
    have hlower := Real.log_lt_log (mul_pos (Real.exp_pos _) hp) hlarge
    rw [Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp] at hlower
    apply abs_le.mpr
    constructor
    · have hh := neg_le_abs (Real.log (F (Real.exp (-(A + J)))))
      linarith
    · have hh := le_abs_self (Real.log (F (Real.exp (-(A + J)))))
      linarith

end ActualPlateaus

end WeakMTWTransport

end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SwitchNumerics
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace WeakMTWTransport

lemma switch_numerical_errors {b r R D C H S eta:ℝ}
    (hb:0 < b) (hD:0 < D) (hr:0 ≤ r) (hC:0 ≤ C) (hH:0 ≤ H) (hS:0 ≤ S)
    (heta:eta ≤ 1/128) (hrb:r ≤ b/2048)
    (hR:b*(H+100) ≤ R) (hbD:b*(16*H+1000) ≤ D)
    (hquad:b*(C+1)*(S+1) ≤ D^2/1048576) :
    r ≤ b/4 ∧ b ≤ D/16 ∧
    b*H+2*r+6*D*(8*b/D)+(C*S)*(8*b/D)^2 ≤ R ∧
    4*eta*D+2*r+12*D*(8*b/D)+2*(C*S)*(8*b/D)^2+b ≤ D ∧
    2*(C*S)*(8*b/D) ≤ 2*D ∧
    2*(8*b/D)*S+2*b*H+2*r ≤ D/4 ∧
    r+(C+1)*(8*b/D)^2*S ≤ b/1024 := by
  have hDp:0 < D^2:=sq_pos_of_pos hD
  have hCS:0 ≤ (C+1)*S:=by positivity
  have hcore:b*((C+1)*S) ≤ D^2/1048576:=by nlinarith only [hquad,mul_nonneg hb.le (by linarith only [hC] : 0 ≤ C+1)]
  have hkin:b*S ≤ D^2/1048576:=by
    have hh:0 ≤ b*C*S:=by positivity
    nlinarith only [hcore,hh]
  have htem: (C+1)*(8*b/D)^2*S ≤ b/16384 := by
    have hh:=mul_le_mul_of_nonneg_right hcore (show 0 ≤ 64*b/D^2 by positivity)
    have he:(b*((C+1)*S))*(64*b/D^2)=(C+1)*(8*b/D)^2*S:=by ring
    have he':(D^2/1048576)*(64*b/D^2)=b/16384:=by field_simp <;> ring
    rwa [he,he'] at hh
  have htemC:(C*S)*(8*b/D)^2 ≤ b/16384:=by
    have hp:0 ≤ S*(8*b/D)^2:=by positivity
    nlinarith only [htem,hp]
  have hlinS:2*(8*b/D)*S ≤ D/65536:=by
    have hh:=mul_le_mul_of_nonneg_right hkin (show 0 ≤ 16/D by positivity)
    have he:(b*S)*(16/D)=2*(8*b/D)*S:=by ring
    have he':(D^2/1048576)*(16/D)=D/65536:=by field_simp <;> ring
    rwa [he,he'] at hh
  have hlinC:2*(C*S)*(8*b/D) ≤ D/65536:=by
    have hh:=mul_le_mul_of_nonneg_right hcore (show 0 ≤ 16/D by positivity)
    have he':(D^2/1048576)*(16/D)=D/65536:=by field_simp <;> ring
    rw [he'] at hh
    have hpos:0 ≤ 16*b*S/D:=by positivity
    calc
      2*(C*S)*(8*b/D) = b*((C+1)*S)*(16/D)-16*b*S/D := by ring
      _ ≤ D/65536 := by linarith only [hh,hpos]
  have he6:6*D*(8*b/D)=48*b:=by field_simp <;> ring
  have he12:12*D*(8*b/D)=96*b:=by field_simp <;> ring
  have heEta:=mul_le_mul_of_nonneg_right heta hD.le
  have hbH:0 ≤ b*H:=mul_nonneg hb.le hH
  refine ⟨by linarith only [hrb,hr],by nlinarith only [hbD,hbH,hb],?_,?_,?_,?_,?_⟩
  · rw [he6]
    nlinarith only [hR,hrb,htemC,hb]
  · rw [he12]
    nlinarith only [heEta,hrb,htemC,hbD,hbH,hb]
  · linarith only [hlinC,hD]
  · nlinarith only [hlinS,hbD,hrb,hb,hD]
  · linarith only [hrb,htem,hb]

end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActualScaleSmallness
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma gap_scale_ratios (A J:ℝ) :
    Real.exp (-(A+J))/lowerGapScale A J=Real.exp (-J/3) ∧
    lowerGapScale A J/upperGapScale A J=Real.exp (-J/3) ∧
    upperGapScale A J/Real.exp (-A)=Real.exp (-J/3) := by
  simp only [lowerGapScale,upperGapScale,←Real.exp_sub]
  constructor
  · congr 1; ring
  constructor <;> congr 1 <;> ring

lemma exists_uniform_plateau_smallness {C eps:ℝ} (hC:0 ≤ C) (heps:0 < eps) :
    ∃J:ℝ,4 ≤ J ∧ Real.exp (2/J) ≤ 1+eps ∧
    ∀A D:ℝ,J^2 ≤ A → 0 < D → |Real.log D| ≤ C+A/J^2+J⁻¹ →
      Real.exp (-(A+J)) ≤ eps*lowerGapScale A J ∧
      lowerGapScale A J ≤ eps*upperGapScale A J ∧
      upperGapScale A J ≤ eps*Real.exp (-A) ∧
      (∀k:ℕ,k ≤ 2 → upperGapScale A J ≤ eps*D^k) := by
  have ht : Tendsto (fun J:ℝ=>Real.exp (2*C+2-J/3)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [sub_eq_add_neg,Function.comp_def,id_eq] using tendsto_const_nhds.add_atBot
      (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<3)))
  have hr : Tendsto (fun J:ℝ=>Real.exp (-J/3)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [Function.comp_def,neg_div,id_eq] using
      (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<3)))
  have hd : Tendsto (fun J:ℝ=>Real.exp (2/J)) atTop (𝓝 1) := by
    simpa only [Real.exp_zero,Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp
      (show Tendsto (fun J:ℝ=>2/J) atTop (𝓝 0) from tendsto_const_nhds.div_atTop tendsto_id)
  obtain ⟨J,hJ,Ht,Hr,Hd⟩ := ((eventually_ge_atTop (4:ℝ)).and
    ((ht.eventually (gt_mem_nhds heps)).and
    ((hr.eventually (gt_mem_nhds heps)).and (hd.eventually (gt_mem_nhds (by linarith : (1:ℝ)<1+eps)))))).exists
  refine ⟨J,hJ,Hd.le,?_⟩
  intro A D hA hD hlog
  have hJ0:0 < J:=by linarith
  have hJ2:16 ≤ J^2:=by nlinarith only [hJ]
  have hA0:0 ≤ A:=(sq_nonneg J).trans hA
  have hfrac:A/J^2 ≤ A/16:=by
    apply div_le_div_of_nonneg_left hA0 (by norm_num) hJ2
  have hinv:J⁻¹ ≤ 1:=by exact inv_le_one_of_one_le₀ (by linarith)
  have hlog': -(C+A/16+1) ≤ Real.log D:=by
    have H:=neg_abs_le (Real.log D)
    linarith only [H,hlog,hfrac,hinv]
  obtain ⟨H1,H2,H3⟩:=gap_scale_ratios A J
  refine ⟨?_,?_,?_,?_⟩
  · exact (div_le_iff₀ (Real.exp_pos _)).mp (H1.le.trans Hr.le)
  · exact (div_le_iff₀ (Real.exp_pos _)).mp (H2.le.trans Hr.le)
  · exact (div_le_iff₀ (Real.exp_pos _)).mp (H3.le.trans Hr.le)
  · intro k hk
    have hex : -(A+J/3)-(k:ℝ)*Real.log D ≤ 2*C+2-J/3 := by
      interval_cases k <;> norm_num <;> nlinarith only [hlog',hA0,hC]
    have He:= (Real.exp_le_exp.mpr hex).trans Ht.le
    have heq: Real.exp (-(A+J/3)-(k:ℝ)*Real.log D)=upperGapScale A J/D^k := by
      rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_log hD]
      rfl
    rw [heq] at He
    exact (div_le_iff₀ (pow_pos hD k)).mp He

end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActualSmallPlateau
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace WeakMTWTransport
section ActualSmallPlateau
variable {M:Type*} [MetricSpace M] [CompactSpace M] [Nonempty M] [MeasurableSpace M]

lemma exists_actual_small_plateau {vol:Measure M} {lam cap:ℝ} {x0:M}
    (hc:(densityDualClass vol lam cap x0).Nonempty)
    (hno:¬ HasPowerUpperBound (classOscillation vol lam cap x0)) {eps:ℝ} (heps:0 < eps) :
    ∃r R bm bp:ℝ,0 < r ∧ 0 < R ∧ 0 < bm ∧ 0 < bp ∧
    ∃uv∈densityDualClass vol lam cap x0,∃x y0 y1:M,
      y0∈gapSection uv.1 uv.2 x r ∧ y1∈gapSection uv.1 uv.2 x r ∧
      (∀y∈gapSection uv.1 uv.2 x r,uv.2 y0 ≤ uv.2 y) ∧
      (∀y∈gapSection uv.1 uv.2 x r,uv.2 y ≤ uv.2 y1) ∧
      sectionOscillation uv.1 uv.2 x r=uv.2 y1-uv.2 y0 ∧ 0 < uv.2 y1-uv.2 y0 ∧
      classOscillation vol lam cap x0 R ≤ (1+eps)*(uv.2 y1-uv.2 y0) ∧
      r ≤ eps*bm ∧ bm ≤ eps*bp ∧ bp ≤ eps*R ∧
      (∀k:ℕ,k ≤ 2 → bp ≤ eps*(uv.2 y1-uv.2 y0)^k) := by
  obtain ⟨J,hJ,heJ,Hs⟩:=exists_uniform_plateau_smallness
    (abs_nonneg (Real.log (1+Metric.diam (univ:Set M)^2))) heps
  obtain ⟨A,uv,huv,x,y0,y1,hA,hy0,hy1,hlo,hhi,he,hD,hR,hlog⟩:=
    exists_actual_plateau_section hc hno (show 1 ≤ J by linarith)
  obtain ⟨hrbm,hbmbp,hbpR,hbpD⟩:=Hs A (uv.2 y1-uv.2 y0) hA hD hlog
  refine ⟨Real.exp (-(A+J)),Real.exp (-A),lowerGapScale A J,upperGapScale A J,
    Real.exp_pos _,Real.exp_pos _,Real.exp_pos _,Real.exp_pos _,uv,huv,x,y0,y1,
    hy0,hy1,hlo,hhi,he,hD,?_,hrbm,hbmbp,hbpR,hbpD⟩
  exact hR.trans (mul_le_mul_of_nonneg_right heJ hD.le)

end ActualSmallPlateau
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_SmallEpsilon
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set

namespace WeakMTWTransport

lemma exists_small_positive (S:Finset ℝ) (hS:∀a∈S,0<a) : ∃e:ℝ,0<e ∧ ∀a∈S,e≤a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨e,he,heS⟩:=ih (fun b hb=>hS b (Finset.mem_insert_of_mem hb))
    refine ⟨min a e,lt_min (hS a (Finset.mem_insert_self _ _)) he,?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (heS b hb)

lemma ratio_mul_le {a e X A B:ℝ} (ha:a ≤ e*X) (hA:0 ≤ A) (hX:0 ≤ X)
    (he:e*A ≤ B) : a*A ≤ B*X := by
  calc a*A ≤ (e*X)*A := mul_le_mul_of_nonneg_right ha hA
       _ = (e*A)*X := by ring
       _ ≤ B*X := mul_le_mul_of_nonneg_right he hX

end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_NonpowerMaximum
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle Metric MeasureTheory
open scoped Topology ContDiff NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section NonpowerMaximum
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.nonpower_maximum (hmtw:WeakMTW (n:=n) (M:=M))
    {lam cap:ℝ} {x0:M} (hc:(densityDualClass (metricVolume n) lam cap x0).Nonempty)
    (hno:¬HasPowerUpperBound (classOscillation (metricVolume n) lam cap x0))
    {M0 K eta C θ:ℝ} (hM:2 ≤ M0) (hK:1 ≤ K) (heta:0 < eta) (heta1:eta ≤ 1/128)
    (hetasmall:eta ≤ templateEps/(24*(128*(M0+3)*(K+1))))
    (hC:0 ≤ C) (hder:∀s,|deriv (outerTemplate M0 K eta) s| ≤ C) (hθ:0 < θ) :
    ∃uv∈densityDualClass (metricVolume n) lam cap x0,∃α D bm bp:ℝ,
      0 < D ∧ 0 < bm ∧ 0 < bp ∧ bp ≤ θ*D ∧ bp/D*centerGamma ≤ 1 ∧ bp/D*C ≤ 1/2 ∧
      (∀z:M,sectionOscillation uv.1 uv.2 z ((2*M0+10)*bp) ≤ (1+eta)*D) ∧
      2*(2*M0+10)*bp ≤ eta*D ∧
      Nonempty (MaximumFamily (n:=n) uv.2 α D bm bp centerTemplate (outerTemplate M0 K eta)) := by
  classical
  let H:ℝ:=2*M0+8
  have hH:0 ≤ H:=by dsimp [H]; linarith only [hM]
  let P:ℝ:=Metric.diam (univ:Set M)
  have hP:0 ≤ P:=Metric.diam_nonneg
  have hγ:=centerGamma_pos
  obtain ⟨Cg,hCg,d,hd,hTaylor⟩:=exists_uniform_cost_upper_taylor (n:=n) (M:=M)
  let S:Finset ℝ:={eta,1/(2^40),1/(H+100),1/(16*H+1000),
    1/(1048576*(Cg+1)*(P^2+1)),d/(16*(P+1)),eta/(2*(H+2)),1/(H+2),θ,
    1/centerGamma,1/(2*(C+1))}
  have hS:∀a∈S,0 < a:=by
    intro a ha
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> positivity
  obtain ⟨e,he,hse⟩:=exists_small_positive S hS
  have heeta:e ≤ eta:=hse _ (by simp [S])
  have he40:e ≤ 1/(2^40):=hse _ (by simp [S])
  have heR:e*(H+100) ≤ 1:=(le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have heD:e*(16*H+1000) ≤ 1:=(le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have heQ:e*(1048576*(Cg+1)*(P^2+1)) ≤ 1:=
    (le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have hed:e*(16*(P+1)) ≤ d:=(le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have heη:e*(2*(H+2)) ≤ eta:=(le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have heHR:e*(H+2) ≤ 1:=(le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have heθ:e ≤ θ:=hse _ (by simp [S])
  have heγ:e*centerGamma ≤ 1:=(le_div_iff₀ hγ).mp (hse _ (by simp [S]))
  have heC:e*(2*(C+1)) ≤ 1:=(le_div_iff₀ (by positivity)).mp (hse _ (by simp [S]))
  have he1:e ≤ 1:=by norm_num at he40; linarith only [he40]
  obtain ⟨r,R,bm,bp,hr,hR,hbm,hbp,uv,huv,x,y0,y1,hy0,hy1,hlo,hhi,hsec,hD,hglobal,
    hrbm,hbmbp,hbpR,hbpPow⟩:=exists_actual_small_plateau hc hno he
  let D:=uv.2 y1-uv.2 y0
  change 0 < D at hD
  change sectionOscillation uv.1 uv.2 x r = D at hsec
  let α:=uv.2 y0
  let b:ℝ:=bp/8192
  have hb:0 < b:=div_pos hbp (by norm_num)
  have hbbp:b ≤ bp:=by dsimp [b]; linarith only [hbp]
  have hbpD:bp ≤ e*D:=by simpa only [pow_one] using hbpPow 1 (by norm_num)
  have hbD':b ≤ e*D:=hbbp.trans hbpD
  have hbpD2:bp ≤ e*D^2:=hbpPow 2 le_rfl
  have hbmle:bm ≤ bp:=hbmbp.trans (by nlinarith only [he1,hbp])
  have hrbp:r ≤ e*bp:=hrbm.trans (mul_le_mul_of_nonneg_left hbmle he.le)
  have hrb:r ≤ b/2048:=by
    have HH:=mul_le_mul_of_nonneg_right he40 hbp.le
    dsimp [b]
    norm_num at HH
    linarith only [hrbp,HH,hbp]
  have hsmallbm:bm ≤ bp/(64*1024^2):=by
    have HH:=mul_le_mul_of_nonneg_right he40 hbp.le
    norm_num at HH ⊢
    linarith only [hbmbp,HH,hbp]
  have hbR:b*(H+100) ≤ R:=by
    simpa only [one_mul] using ratio_mul_le (hbbp.trans hbpR) (by positivity) hR.le heR
  have hbDb:b*(16*H+1000) ≤ D:=by
    simpa only [one_mul] using ratio_mul_le hbD' (by positivity) hD.le heD
  obtain ⟨p,hp,hep⟩:=exists_minimizing_vector (n:=n) x y0
  obtain ⟨q,hq,heq⟩:=exists_minimizing_vector (n:=n) x y1
  have hpP:‖p‖ ≤ P:=minimizing_norm_le_diam hp
  have hpP2:‖p‖^2 ≤ P^2:=sq_le_sq₀ (norm_nonneg _) hP |>.mpr hpP
  have hbQuad:b*(Cg+1)*(‖p‖^2+1) ≤ D^2/1048576:=by
    have hh:=ratio_mul_le (hbbp.trans hbpD2) (by positivity) (sq_nonneg D) heQ
    rw [one_mul] at hh
    have hmul:=mul_le_mul_of_nonneg_left (add_le_add_right hpP2 1) (show 0 ≤ b*(Cg+1) by positivity)
    nlinarith only [hh,hmul]
  obtain ⟨hrb4,hbD16,hanchor,hlower,hlower',hnorm,herror⟩:=switch_numerical_errors hb hD hr.le hCg.le hH
    (sq_nonneg ‖p‖) heta1 hrb hbR hbDb hbQuad
  have hsdisp:‖(8*b/D:ℝ) • p‖ < d:=by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 8*b/D)]
    have hratio:b/D ≤ e:=(div_le_iff₀ hD).mpr hbD'
    have hh:=mul_le_mul_of_nonneg_right hratio (show 0 ≤ 8*‖p‖ by positivity)
    have hhP:=mul_le_mul_of_nonneg_left hpP (show 0 ≤ 8*e by positivity)
    calc
      (8*b/D)*‖p‖ = (b/D)*(8*‖p‖) := by ring
      _ ≤ e*(8*‖p‖) := hh
      _ = 8*e*‖p‖ := by ring
      _ ≤ 8*e*P := hhP
      _ < d := by nlinarith only [hed,he,mul_nonneg he.le hP]
  have hdual:=densityDualClass_isDual huv
  have ha:uv.2 (riemannianExp x p)=α:=by rw [hep]
  have ha1:uv.2 (riemannianExp x q)=α+D:=by rw [heq]; dsimp [α,D] <;> ring
  have hpsec:p∈liftedGapSection uv.1 uv.2 x r:=mem_liftedGapSection_iff.mpr ⟨hp,by rwa [hep]⟩
  have hqsec:q∈liftedGapSection uv.1 uv.2 x r:=mem_liftedGapSection_iff.mpr ⟨hq,by rwa [heq]⟩
  have hangle:‖p‖^2-inner ℝ p q ≤ 6*D:=
    (hmtw.section_initial_logs uv.1.continuous uv.2.continuous hdual hr.le
      (by linarith only [hrb4,hbD16,hD]) hpsec hqsec ha ha1 hsec.le).2.2.1
  have hosc (z:M):sectionOscillation uv.1 uv.2 z R ≤ (1+eta)*D:=by
    apply (sectionOscillation_le_classOscillation huv z hR.le).trans
    exact hglobal.trans (mul_le_mul_of_nonneg_right (add_le_add_right heeta 1) hD.le)
  let Bo:=outerTemplate M0 K eta
  have hBo:ContDiff ℝ ∞ Bo:=outerTemplate_smooth _ _ _
  have hob (s):0 ≤ Bo s ∧ Bo s ≤ H:=⟨outerTemplate_nonneg hM hK heta heta1 hetasmall,
    outerTemplate_upper hM hK heta heta1 hetasmall⟩
  obtain ⟨y,hy⟩:=hmtw.switch_to_positive_excess uv.1.continuous uv.2.continuous hdual hp hq hBo.continuous
    ha ha1 hb hD hr.le hR.le hCg.le (mem_liftedGapSection_iff.mp hpsec).2 (mem_liftedGapSection_iff.mp hqsec).2 hangle heta.le heta1 hrb4 hbD16 hob
    (by dsimp [Bo]; rw [outerTemplate_zero_level heta heta1,templateEps_eq]; norm_num)
    (outerTemplate_zero heta le_rfl)
    (fun s hs=>outerTemplate_lower hM hK heta heta1 hetasmall (by linarith only [hs,heta1]))
    (fun s hs=>outerTemplate_barrier hM hK heta heta1 hs.1 hs.2)
    (fun s=>(centerTemplate_bounds s).1.le) (fun s hs=>by simpa only [templateEps_eq] using centerTemplate_left hs)
    hsdisp hanchor hosc hlower hlower' hnorm herror hTaylor
  have hγsmall:bp/D*centerGamma ≤ 1:=by
    have hh:=ratio_mul_le hbpD hγ.le hD.le heγ
    rw [one_mul] at hh
    calc bp/D*centerGamma = (bp*centerGamma)/D := by ring
         _ ≤ 1 := (div_le_iff₀ hD).mpr (by simpa only [one_mul] using hh)
  have hCsmall:bp/D*C ≤ 1/2:=by
    have heC':e*C ≤ 1/2:=by nlinarith only [heC,he]
    have hh:=ratio_mul_le hbpD hC hD.le heC'
    calc bp/D*C = (bp*C)/D := by ring
         _ ≤ 1/2 := (div_le_iff₀ hD).mpr hh
  have hsCenter (s:ℝ) (hs:s∈Icc bm bp):s/D*(centerGamma/2) ≤ 1/2:=by
    have hh:=mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hD).mpr hs.2) hγ.le
    nlinarith only [hh,hγsmall]
  have hmono (s:ℝ) (hs:s∈Icc bm bp):Monotone (fun t=>modifiedScalar α D centerTemplate (s,t)):=
    (modifiedScalar_strictMono centerTemplate_smooth (by positivity) hD (hbm.le.trans hs.1)
      (hsCenter s hs) exact_center_deriv_abs α).monotone
  have hLipφ (s:ℝ) (hs:s∈Icc bm bp):LipschitzWith 2 (fun t=>modifiedScalar α D centerTemplate (s,t)):=
    modifiedScalar_lipschitz centerTemplate_smooth (by positivity) hD (hbm.le.trans hs.1)
      (hsCenter s hs) exact_center_deriv_abs α
  let Lv:ℝ≥0:=⟨P,hP⟩
  have hvL:LipschitzWith Lv (uv.2:M → ℝ):=by
    rw [hdual.2]
    exact cTransform_lipschitz uv.1.continuous (fun x y=>Metric.dist_le_diam_of_mem
      isCompact_univ.isBounded (mem_univ x) (mem_univ y))
  obtain ⟨A,hA⟩:=isCompact_univ.exists_bound_of_continuousOn uv.2.continuous.continuousOn
  have hrange:∀y:M,cTransform uv.1 y∈Icc (-A) A:=by
    intro y
    rw [←hdual.2]
    exact abs_le.mp (hA y (mem_univ y))
  obtain ⟨δ,hδ,hreg⟩:=uniform_family_short_mdifferentiable (n:=n) (M:=M)
    (modifiedScalar_contDiff centerTemplate_smooth α D) isCompact_Icc hmono hLipφ (-A) A
  have hL:∀s∈Icc bm bp,LipschitzWith (2*Lv) (modifiedDatum uv.2 α D s centerTemplate):=
    fun s hs=>(hLipφ s hs).comp hvL
  have hreg':∀s∈Icc bm bp,∀τ:ℝ,0 < τ → τ < δ →
      MDifferentiable 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax τ (modifiedDatum uv.2 α D s centerTemplate)):=by
    intro s hs τ hτ hτδ
    change MDifferentiable _ _ (hopfLax τ (fun y=>uv.2 y+s*centerTemplate ((uv.2 y-α)/D)))
    simpa only [←hdual.2,modifiedScalar] using hreg s hs uv.1 uv.1.continuous hrange τ hτ hτδ
  have hF:=hmtw.exists_maximum_family uv.2.continuous centerTemplate_smooth.continuous hBo.continuous hob
    hbp hbm.le hsmallbm
    (fun s hs z=>modified_excess_upper uv.1.continuous uv.2.continuous hdual hBo.continuous
      (hbm.le.trans hs.1) (fun t=>(hob t).1) (fun t=>(centerTemplate_bounds t).2.le) z)
    (show ∃y,bp/(8*1024^2) ≤ modifiedExcess uv.2 α D (bp/(8*1024)) centerTemplate Bo y from by
      refine ⟨y,?_⟩
      simpa only [b,show (8192:ℝ)=8*1024 by norm_num,div_div,pow_two,mul_assoc] using hy)
    hL hδ hreg'
  refine ⟨uv,huv,α,D,bm,bp,hD,hbm,hbp,hbpD.trans (mul_le_mul_of_nonneg_right heθ hD.le),
    hγsmall,hCsmall,?_,?_,hF⟩
  · intro z
    apply le_trans (sectionOscillation_mono uv.2.continuous hdual z (by positivity) ?_) (hosc z)
    have hh:=ratio_mul_le hbpR (show 0 ≤ H+2 by positivity) hR.le heHR
    dsimp [H] at hh
    nlinarith only [hh]
  · have hh:=ratio_mul_le hbpD (show 0 ≤ 2*(H+2) by positivity) hD.le heη
    dsimp [H] at hh
    nlinarith only [hh]

end NonpowerMaximum
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_ClassPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section ClassPower
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.class_power_oai (hmtw:WeakMTW (n:=n) (M:=M)) (hn:0 < n)
    {lam cap:ℝ} (hlam:0 < lam) (hcap:lam ≤ cap) (x0:M)
    (hc:(densityDualClass (metricVolume n) lam cap x0).Nonempty) :
    HasPowerUpperBound (classOscillation (metricVolume n) lam cap x0) := by
  classical
  by_contra hno
  obtain ⟨B,hB,eps,heps,HB⟩:=hmtw.maximum_template_bound hn hlam hcap
  let M0:ℝ:=12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)
  let μ:ℝ:=(1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ))
  have hM:2 ≤ M0:=by dsimp [M0]; have h:=Nat.cast_nonneg (α:=ℝ) (Module.finrank ℝ (Model n)); linarith
  have hμ:0 < μ:=by dsimp [μ] <;> positivity
  have hγ:=centerGamma_pos
  let K:ℝ:=1+8*centerGamma^2*(B+1)/μ^(n-1)
  have hK:1 ≤ K:=by dsimp [K]; exact le_add_of_nonneg_right (by positivity)
  let eta:ℝ:=min (1/128) (templateEps/(24*(128*(M0+3)*(K+1))))
  have heta:0 < eta:=by dsimp [eta]; rw [templateEps_eq]; positivity
  have heta1:eta ≤ 1/128:=min_le_left _ _
  have hetasmall:eta ≤ templateEps/(24*(128*(M0+3)*(K+1))):=min_le_right _ _
  obtain ⟨C,hC,hder⟩:=exists_outerTemplate_deriv_bound (M0:=M0) (K:=K) heta heta1
  let θ:ℝ:=eps/centerGamma
  have hθ:0 < θ:=by dsimp [θ] <;> positivity
  obtain ⟨uv,huv,α,D,bm,bp,hD,hbm,hbp,hsmall,hcent,hout,hosc,herror,⟨F⟩⟩:=
    hmtw.nonpower_maximum hc hno hM hK heta heta1 hetasmall hC hder hθ
  have hclose:bp/D*centerGamma/2 < eps:=by
    have hh:bp/D ≤ θ:=(div_le_iff₀ hD).mpr hsmall
    have HH:=mul_le_mul_of_nonneg_right hh hγ.le
    have he:θ*centerGamma=eps:=by dsimp [θ]; field_simp
    rw [he] at HH
    linarith only [HH,heps]
  have H:=HB K eta hK heta heta1 hetasmall x0 uv huv α D bm bp hD hbm hbp hcent hclose
    C hC hder hout hosc herror F
  change μ^(n-1)*K/(8*centerGamma^2) ≤ B at H
  have he:μ^(n-1)*K/(8*centerGamma^2)=μ^(n-1)/(8*centerGamma^2)+(B+1):=by
    dsimp only [K]
    field_simp
  rw [he] at H
  have hh:0 ≤ μ^(n-1)/(8*centerGamma^2):=by positivity
  linarith only [H,hh]

end ClassPower
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.class_power_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.class_power_oai.{u_1}
