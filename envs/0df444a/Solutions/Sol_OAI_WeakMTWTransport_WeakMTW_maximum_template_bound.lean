-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.maximum_template_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:43:32.101681+00:00
-- url     : https://prove2.me/submissions/6ce6ad48-9b8e-4861-ac6b-094ac553bc96

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
import Definitions.Def_OAIQ232A031
import Theorems.Thm_OAI_WeakMTWTransport_MaximumFamily_eventually_jensen_first
import Theorems.Thm_OAI_WeakMTWTransport_MaximumJensenFamily_selected_pole_compact
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_maximum_simultaneous
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_uniform_three_determinant_closure
import Theorems.Thm_OAI_WeakMTWTransport_eventual_lower_bound_of_center_gain
import Theorems.Thm_OAI_WeakMTWTransport_exists_density_original_center_good
import Theorems.Thm_OAI_WeakMTWTransport_exists_maximum_center_gain
import Theorems.Thm_OAI_WeakMTWTransport_original_chart_good_null

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

lemma modifiedScalar_second {B:ℝ → ℝ} (hB:ContDiff ℝ ∞ B) (a D b s:ℝ) :
    iteratedDeriv 2 (fun x=>modifiedScalar a D B (b,x)) s=b/D^2*iteratedDeriv 2 B ((s-a)/D) := by
  have hb:ContDiff ℝ ∞ (deriv B):=(contDiff_infty_iff_deriv.mp hB).2
  have H:= (hasDerivAt_const s (1:ℝ)).add (((hb.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) ((s-a)/D)).hasDerivAt.comp s
    (((hasDerivAt_id s).sub_const a).div_const D)).const_mul (b/D))
  have heq:deriv (fun x=>modifiedScalar a D B (b,x))=(fun x=>1+b/D*deriv B ((x-a)/D)) :=
    funext (modifiedScalar_deriv hB a D b)
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [heq]
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

lemma centerTemplate_right {s:ℝ} (hs : 3/4 ≤ s) : centerTemplate s < 0 := by
  have hs' : -centerGamma*(s-5/8) < 0 := by nlinarith [centerGamma_pos]
  have he : Real.exp (-centerGamma*(s-5/8)) < 1 := Real.exp_lt_one_iff.mpr hs'
  have hden : 0 < 1+Real.exp (-centerGamma*(s-5/8)) := by positivity
  have HH : 1 < 2/(1+Real.exp (-centerGamma*(s-5/8))) :=
    (lt_div_iff₀ hden).mpr (by linarith only [he])
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

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OuterTemplate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma contDiff_primitive {f:ℝ → ℝ} (hf:ContDiff ℝ ∞ f) (a:ℝ) :
    ContDiff ℝ ∞ (fun s=>∫ q in a..s,f q) := by
  apply contDiff_infty_iff_deriv.mpr
  have hd:∀s,HasDerivAt (fun t=>∫ q in a..t,f q) (f s) s:=fun s=>
    intervalIntegral.integral_hasDerivAt_right (hf.continuous.intervalIntegrable _ _)
      hf.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuous.continuousAt
  exact ⟨fun s=>(hd s).differentiableAt,by simpa only [funext (fun s=>(hd s).deriv)] using hf⟩

lemma outerW_contDiff (K M η:ℝ) : ContDiff ℝ ∞ (outerW K M η) := by
  unfold outerW
  exact ((contDiff_const.sub (contDiff_const.mul contDiff_id)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _))).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)))

lemma outerJ_contDiff (K M η:ℝ) : ContDiff ℝ ∞ (outerJ K M η) :=
  contDiff_const.add (contDiff_primitive (outerW_contDiff K M η) 0)

lemma outerProfile_contDiff (K M η:ℝ) : ContDiff ℝ ∞ (outerProfile K M η) := by
  unfold outerProfile
  exact (outerJ_contDiff K M η).mul (contDiff_const.sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)))

lemma outerJ_hasDerivAt (K M η s:ℝ) : HasDerivAt (outerJ K M η) (outerW K M η s) s := by
  have hc:Continuous (outerW K M η):=(outerW_contDiff K M η).continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

lemma outerW_zero_right {K M η s:ℝ} (hK:1≤K) (hs:2/(128*(K+1))≤ s) : outerW K M η s=0 := by
  have hh:0<1/(128*(K+1)):=by positivity
  have hs' : 2*(1/(128*(K+1))) ≤ s := by convert hs using 1 <;> first | rfl | ring
  unfold outerW
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hh).mpr (by linarith only [hs']))]
  ring

lemma outerW_nonneg {K M η:ℝ} (hK:1≤K) (hM:2≤M) (_:0<η) (s:ℝ) :
    0≤outerW K M η s := by
  by_cases hs:2/(128*(K+1))≤ s
  · rw [outerW_zero_right hK hs]
  · have hs':s<2/(128*(K+1)):=lt_of_not_ge hs
    have hb:2/(128*(K+1))<128*(M+3):=by
      apply (div_lt_iff₀ (by positivity : 0<128*(K+1))).mpr
      nlinarith
    dsimp only [outerW]
    exact mul_nonneg (mul_nonneg (by nlinarith) (Real.smoothTransition.nonneg _))
      (sub_nonneg.mpr (Real.smoothTransition.le_one _))

lemma outerJ_monotone {K M η:ℝ} (hK:1≤K) (hM:2≤M) (hη:0<η) :
    Monotone (outerJ K M η) := by
  apply monotone_of_deriv_nonneg ((outerJ_contDiff K M η).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  intro s
  rw [(outerJ_hasDerivAt K M η s).deriv]
  exact outerW_nonneg hK hM hη s

lemma outerW_affine {K M η s:ℝ} (hK:1≤K) (hη:0<η)
    (hs₁:-2*η≤ s) (hs₂:s≤1/(128*(K+1))) :
    outerW K M η s=128*(M+3)*(K+1)-(K+1)*s := by
  have hh:0<1/(128*(K+1)):=by positivity
  unfold outerW
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hη).mpr (by linarith)),
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le)]
  ring

lemma outerProfile_left {K M η s:ℝ} (hη:0<η) (hs:s≤1-η) :
    outerProfile K M η s=outerJ K M η s := by
  unfold outerProfile
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le)]
  ring

lemma outerJ_zero (K M η:ℝ) : outerJ K M η 0=1+(1/2048:ℝ) := by
  simp only [outerJ,intervalIntegral.integral_same,add_zero]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OuterBounds
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma outerJ_add_integral (K M η a b:ℝ) :
    outerJ K M η a + ∫q in a..b,outerW K M η q = outerJ K M η b := by
  have hc := (outerW_contDiff K M η).continuous
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
  unfold outerJ
  linarith only [hh]
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_OuterCurvature
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma deriv_eq_of_eqOn_interval {f g : ℝ → ℝ} {a b x : ℝ}
    (hab : a<b) (hx : x∈Icc a b) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (he : EqOn f g (Icc a b))  :  deriv f x=deriv g x  :=  by
  exact (uniqueDiffOn_Icc hab x hx).eq_deriv _ hf.hasDerivAt.hasDerivWithinAt
    (hg.hasDerivAt.hasDerivWithinAt.congr (fun y hy=>he hy) (he hx))

lemma outerJ_affine_integral {K M η : ℝ} (hK : 1≤K) (hη : 0<η)  :
    outerJ K M η (1/(128*(K+1)))-outerJ K M η 0=
      M+3-1/(32768*(K+1))  :=  by
  let h : ℝ := 1/(128*(K+1))
  have hh : 0<h := by dsimp only [h] <;> positivity
  have he :  (∫s in (0 : ℝ)..h,outerW K M η s)=
      ∫s in (0 : ℝ)..h,(128*(M+3)*(K+1)-(K+1)*s)  :=  by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hh.le] at hs
    exact outerW_affine hK hη (by linarith [hs.1]) hs.2
  have hd : ∀s : ℝ,HasDerivAt (fun z : ℝ=>128*(M+3)*(K+1)*z-(K+1)*z^2/2)
      (128*(M+3)*(K+1)-(K+1)*s) s := by
    intro s
    convert! ((hasDerivAt_id s).const_mul (128*(M+3)*(K+1))).sub
      ((((hasDerivAt_id s).pow 2).const_mul (K+1)).div_const 2) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>hd s)
    ((continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable _ _)] at he
  have H := outerJ_add_integral K M η 0 h
  have heq : 128*(M+3)*(K+1)*h-(K+1)*h^2/2-
      (128*(M+3)*(K+1)*(0 : ℝ)-(K+1)*(0 : ℝ)^2/2)=M+3-1/(32768*(K+1)) := by
    dsimp only [h]
    field_simp [show K+1≠0 by linarith]
    ring
  rw [heq] at he
  linarith only [H,he]

lemma outerJ_barrier {K M η : ℝ} (hK : 1≤K) (_ : 2≤M) (hη : 0<η)  :
    outerJ K M η 0+M+1 < outerJ K M η (1/(128*(K+1)))  :=  by
  have H := outerJ_affine_integral hK hη (M := M)
  have hh : 1/(32768*(K+1)) < (1 : ℝ)  :=  by
    apply (div_lt_iff₀ (by positivity  :  0<32768*(K+1))).mpr
    linarith
  linarith only [H,hh]

lemma outerProfile_forces_affine {K M η s : ℝ} (hK : 1≤K) (hM : 2≤M) (hη : 0<η)
    (hs : s≤1-η) (hcap : outerProfile K M η s≤M)  :  s<1/(128*(K+1))  :=  by
  rw [outerProfile_left hη hs] at hcap
  by_contra hh
  have HM := (outerJ_monotone hK hM hη) (le_of_not_gt hh)
  have HB := outerJ_barrier hK hM hη
  rw [outerJ_zero] at HB
  linarith only [hcap,HM,HB]

lemma outerProfile_derivatives_left {K M η s : ℝ} (hη : 0<η) (hs : s≤1-η)  :
    deriv (outerProfile K M η) s=outerW K M η s ∧
    iteratedDeriv 2 (outerProfile K M η) s=deriv (outerW K M η) s  :=  by
  have hd : ∀x∈Iic (1-η),deriv (outerProfile K M η) x=deriv (outerJ K M η) x := by
    intro x hx
    exact (uniqueDiffOn_Iic (1-η) x hx).eq_deriv _
      (((outerProfile_contDiff K M η).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasDerivAt.hasDerivWithinAt)
      ((((outerJ_contDiff K M η).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasDerivAt.hasDerivWithinAt).congr
        (fun y hy=>outerProfile_left hη hy) (outerProfile_left hη hx))
  have hdiff : deriv (outerJ K M η)=outerW K M η := funext (fun x=>(outerJ_hasDerivAt K M η x).deriv)
  constructor
  · rw [hd s hs,hdiff]
  · simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    exact (uniqueDiffOn_Iic (1-η) s hs).eq_deriv _
      ((((contDiff_infty_iff_deriv.mp (outerProfile_contDiff K M η)).2).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) s).hasDerivAt.hasDerivWithinAt)
      ((((outerW_contDiff K M η).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) s).hasDerivAt.hasDerivWithinAt).congr
        (fun y hy=>by rw [hd y hy,hdiff]) (by rw [hd s hs,hdiff]))

lemma outerProfile_curvature {K M η s : ℝ} (hK : 1≤K) (hM : 2≤M) (hη : 0<η)
    (hs : -2 * η ≤ s) (hs' : s ≤ 1 - η) (hcap : outerProfile K M η s≤M)  :
    0<deriv (outerProfile K M η) s ∧ iteratedDeriv 2 (outerProfile K M η) s≤ -K  :=  by
  have hhi := outerProfile_forces_affine hK hM hη hs' hcap
  have hab : -2*η<1/(128*(K+1)) := by
    have hp : 0<1/(128*(K+1)) := by positivity
    linarith
  have hder := deriv_eq_of_eqOn_interval hab ⟨hs,hhi.le⟩
    ((outerW_contDiff K M η).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) s)
    ((((hasDerivAt_id s).const_mul (K+1)).const_sub (128*(M+3)*(K+1))).differentiableAt)
    (fun y hy=>outerW_affine hK hη hy.1 hy.2)
  have hf : deriv (fun x : ℝ=>128*(M+3)*(K+1)-(K+1)*x) s= -(K+1) := by
    simp
  simp only [id_eq] at hder
  rw [hf] at hder
  obtain ⟨H1,H2⟩ := outerProfile_derivatives_left hη hs'
  rw [H1,H2,outerW_affine hK hη hs hhi.le,hder]
  have hh : 1/(128*(K+1)) < 128*(M+3) := by
    apply (div_lt_iff₀ (by positivity  :  0<128*(K+1))).mpr
    nlinarith
  constructor <;> nlinarith
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

lemma centerTemplate_second (s:ℝ) :
    iteratedDeriv 2 centerTemplate s=centerGamma*centerTemplate s*deriv centerTemplate s := by
  have H : deriv centerTemplate=(fun s=> -(centerGamma/2)*(1-(centerTemplate s)^2)) :=
    funext centerTemplate_deriv_polynomial
  have HD:=(((hasDerivAt_centerTemplate s).pow 2).const_sub 1).const_mul (-(centerGamma/2))
  have HD' : HasDerivAt (fun x=> -(centerGamma/2)*(1-(centerTemplate x)^2))
      (centerGamma*centerTemplate s*deriv centerTemplate s) s := by
    convert! HD using 1
    all_goals try with_reducible_and_instances rfl
    rw [(hasDerivAt_centerTemplate s).deriv]
    norm_num
    ring
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  calc
    deriv (deriv centerTemplate) s = deriv (fun x=> -(centerGamma/2)*(1-(centerTemplate x)^2)) s :=
      congrArg (fun f=>deriv f s) H
    _ = _ := HD'.deriv

lemma centerTemplate_deriv_bound (s:ℝ) :
    0 < -deriv centerTemplate s ∧ -deriv centerTemplate s ≤ centerGamma/2 := by
  refine ⟨neg_pos.mpr (centerTemplate_deriv_neg s),?_⟩
  rw [centerTemplate_deriv_polynomial]
  nlinarith only [centerGamma_pos,sq_nonneg (centerTemplate s)]

lemma centerTemplate_curvature {s:ℝ} (hs:0 < centerTemplate s) :
    iteratedDeriv 2 centerTemplate s < 0 ∧
    -iteratedDeriv 2 centerTemplate s ≤ centerGamma*(-deriv centerTemplate s) ∧
    -iteratedDeriv 2 centerTemplate s ≤ centerGamma^2/2 := by
  rw [centerTemplate_second]
  have hd:=centerTemplate_deriv_neg s
  have hb:=(centerTemplate_bounds s).2
  have hu:=(centerTemplate_deriv_bound s).2
  have H : -(centerGamma*centerTemplate s*deriv centerTemplate s) ≤
      centerGamma*(-deriv centerTemplate s) := by
    nlinarith only [mul_nonneg centerGamma_pos.le (neg_nonneg.mpr hd.le),hb]
  refine ⟨mul_neg_of_pos_of_neg (mul_pos centerGamma_pos hs) hd,H,?_⟩
  nlinarith only [H,mul_le_mul_of_nonneg_left hu centerGamma_pos.le]

lemma outerTemplate_eq_profile (M K eta:ℝ) : outerTemplate M K eta=outerProfile K M eta := by
  funext s
  simp only [outerTemplate,outerPrimitive,outerProfile,outerJ,templateEps_eq]
  congr 2
  norm_num

lemma exact_outer_curvature {M K eta s:ℝ} (hK:1 ≤ K) (hM:2 ≤ M) (heta:0 < eta)
    (hs:-2*eta ≤ s) (hs':s ≤ 1-eta) (hcap:outerTemplate M K eta s ≤ M) :
    0 < deriv (outerTemplate M K eta) s ∧
    iteratedDeriv 2 (outerTemplate M K eta) s ≤ -K := by
  rw [outerTemplate_eq_profile] at hcap ⊢
  exact outerProfile_curvature hK hM heta hs hs' hcap

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

lemma exact_center_slope_curvature {a D b s:ℝ} (hD:0 < D) (hb:0 < b)
    (hsmall:b/D*centerGamma ≤ 1) (hs:0 < centerTemplate ((s-a)/D)) :
    let l:=deriv (fun x=>modifiedScalar a D centerTemplate (b,x)) s
    let k:=iteratedDeriv 2 (fun x=>modifiedScalar a D centerTemplate (b,x)) s
    (1:ℝ)/2 ≤ l ∧ l<1 ∧ k<0 ∧
      -k/l^2 ≤ 2*centerGamma^2*b/D^2 ∧
      -k/l^2 ≤ 4*centerGamma*(1-l)/D := by
  dsimp only
  rw [modifiedScalar_deriv centerTemplate_smooth,modifiedScalar_second centerTemplate_smooth]
  let u:=deriv centerTemplate ((s-a)/D)
  let v:=iteratedDeriv 2 centerTemplate ((s-a)/D)
  have hu:=centerTemplate_deriv_neg ((s-a)/D)
  obtain ⟨hv,hv1,hv2⟩:=centerTemplate_curvature hs
  have hu2:=(centerTemplate_deriv_bound ((s-a)/D)).2
  have hp:0 < b/D:=div_pos hb hD
  have hp2:0 < b/D^2:=div_pos hb (sq_pos_of_pos hD)
  have hl:(1:ℝ)/2 ≤ 1+b/D*u:=by
    have H:=mul_le_mul_of_nonneg_left hu2 hp.le
    dsimp only [u]
    nlinarith only [H,hsmall]
  have hl2:1/4 ≤ (1+b/D*u)^2:=by nlinarith only [hl,sq_nonneg (1+b/D*u-1/2)]
  have hl0:0 < (1+b/D*u)^2:=lt_of_lt_of_le (by norm_num) hl2
  have hk0:0 ≤ -(b/D^2*v):=by dsimp [v]; exact neg_nonneg.mpr (mul_neg_of_pos_of_neg hp2 hv).le
  refine ⟨hl,?_,mul_neg_of_pos_of_neg hp2 hv,?_,?_⟩
  · have H:=mul_neg_of_pos_of_neg hp hu
    dsimp only [u] at hl ⊢
    linarith only [H]
  · apply (div_le_iff₀ hl0).mpr
    have H:=mul_le_mul_of_nonneg_left hv2 hp2.le
    have Q:=mul_le_mul_of_nonneg_left hl2 (show 0 ≤ 2*centerGamma^2*b/D^2 by positivity)
    have he : 2*centerGamma^2*b/D^2*(1/4)=b/D^2*(centerGamma^2/2) := by ring
    rw [he] at Q
    dsimp only [u] at Q ⊢
    linarith only [H,Q]
  · apply (div_le_iff₀ hl0).mpr
    have H:=mul_le_mul_of_nonneg_left hv1 hp2.le
    have Q:=mul_le_mul_of_nonneg_left hl2
      (show 0 ≤ 4*centerGamma*(1-(1+b/D*u))/D by
        have ht:0 ≤ 1-(1+b/D*u):=by
          have H:=mul_neg_of_pos_of_neg hp hu
          dsimp only [u]
          linarith only [H]
        exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) centerGamma_pos.le) ht) hD.le)
    have he:4*centerGamma*(1-(1+b/D*u))/D*(1/4)=b/D^2*(centerGamma*(-u)):=by
      field_simp
      ring
    rw [he] at Q
    dsimp only [u] at Q ⊢
    linarith only [H,Q]

lemma exact_outer_slope_curvature {M K eta a D b s C:ℝ}
    (hM:2 ≤ M) (hK:1 ≤ K) (heta:0 < eta) (hD:0 < D) (hb:0 < b)
    (hC:0 ≤ C) (hder:∀t,|deriv (outerTemplate M K eta) t|≤C) (hsmall:b/D*C ≤ 1/2)
    (hs:-2*eta ≤ (s-a)/D) (hs':(s-a)/D ≤ 1-eta)
    (hcap:outerTemplate M K eta ((s-a)/D) ≤ M) :
    let l:=deriv (fun x=>modifiedScalar a D (outerTemplate M K eta) (b,x)) s
    let k:=iteratedDeriv 2 (fun x=>modifiedScalar a D (outerTemplate M K eta) (b,x)) s
    1 < l ∧ l ≤ 2 ∧ k < 0 ∧ K*b/(4*D^2) ≤ -k/l^2 := by
  dsimp only
  have hupper:=(modifiedScalar_slope_bounds (outerTemplate_smooth M K eta) hC hD hb.le hsmall hder a s).2
  rw [modifiedScalar_deriv (outerTemplate_smooth M K eta)] at hupper ⊢
  rw [modifiedScalar_second (outerTemplate_smooth M K eta)]
  obtain ⟨hd,hdd⟩:=exact_outer_curvature hK hM heta hs hs' hcap
  let l:=1+b/D*deriv (outerTemplate M K eta) ((s-a)/D)
  have hlo:1<l:=by
    have H:=mul_pos (div_pos hb hD) hd
    dsimp only [l]
    linarith only [H]
  have hl2:l ^ 2 ≤ 4:=by dsimp only [l]; nlinarith only [hupper,hlo]
  have hkk:iteratedDeriv 2 (outerTemplate M K eta) ((s-a)/D)<0:=by linarith only [hdd,hK]
  refine ⟨hlo,by linarith only [hupper],mul_neg_of_pos_of_neg (by positivity) hkk,?_⟩
  apply (le_div_iff₀ (sq_pos_of_pos (zero_lt_one.trans hlo))).mpr
  have H:=mul_le_mul_of_nonneg_left hdd (show 0 ≤ b/D^2 by positivity)
  have Q:=mul_le_mul_of_nonneg_left hl2 (show 0 ≤ K*b/(4*D^2) by positivity)
  have he:(K*b/(4*D^2))*4=(b/D^2)*K:=by ring
  rw [he] at Q
  dsimp only [l] at Q
  nlinarith only [H,Q]

lemma scalar_determinant_gain {n:ℕ} {mu m K gamma b D cc co V W:ℝ}
    (hmu:0 < mu) (hm:mu ≤ m) (hK:0 < K) (hgamma:0 < gamma)
    (hb:0 < b) (hD:0 < D) (hV:0 ≤ V) (hW:0 ≤ W)
    (hc:cc ≤ 2*gamma^2*b/D^2) (ho:K*b/(4*D^2) ≤ co)
    (hdet:co*m^(n-1)*V ≤ cc*W) :
    (mu^(n-1)*K/(8*gamma^2))*V ≤ W := by
  have hp:=pow_le_pow_left₀ hmu.le hm (n-1)
  have hmul:mu^(n-1)*V ≤ m^(n-1)*V:=mul_le_mul_of_nonneg_right hp hV
  have h0:0 ≤ K*b/(4*D^2):=by positivity
  have h1:=mul_le_mul_of_nonneg_left hmul h0
  have h2:=mul_le_mul_of_nonneg_right ho (show 0 ≤ m^(n-1)*V from mul_nonneg (pow_nonneg (hmu.le.trans hm) _) hV)
  have h3:=mul_le_mul_of_nonneg_right hc hW
  have hh:K*b/(4*D^2)*(mu^(n-1)*V) ≤ (2*gamma^2*b/D^2)*W:=by
    calc
      _ ≤ K*b/(4*D^2)*(m^(n-1)*V) := h1
      _ ≤ co*(m^(n-1)*V) := h2
      _ = co*m^(n-1)*V := by ring
      _ ≤ cc*W := hdet
      _ ≤ _ := h3
  have he:K*b/(4*D^2)*(mu^(n-1)*V) = (2*gamma^2*b/D^2)*((mu^(n-1)*K/(8*gamma^2))*V):=by
    field_simp
    ring
  rw [he] at hh
  exact (mul_le_mul_iff_right₀ (show 0 < 2*gamma^2*b/D^2 by positivity)).mp hh

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

lemma exact_center_slope_small {a D b s eps:ℝ} (hD:0 < D) (hb:0 ≤ b)
    (hsmall:b/D*centerGamma/2 < eps) :
    |deriv (fun x=>modifiedScalar a D centerTemplate (b,x)) s-1| < eps := by
  rw [modifiedScalar_deriv centerTemplate_smooth,add_sub_cancel_left,abs_mul,
    abs_of_nonneg (div_nonneg hb hD.le)]
  have H:=mul_le_mul_of_nonneg_left (exact_center_deriv_abs ((s-a)/D)) (div_nonneg hb hD.le)
  exact H.trans_lt (by simpa only [mul_div_assoc] using hsmall)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_GraphCoordinates
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
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] in
lemma graph_coordinates_at_center (q : TangentBundle 𝓘(ℝ,Model n) M) :
    graphVelocityCoordinate q.1 q=q.2 := by
  unfold graphVelocityCoordinate
  rw [tangent_chart_apply]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source q.1)
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActiveLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma positive_barycentric_restriction {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (p : ι → E) (w : ι → ℝ)
    (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) :
    let κ := {i : ι // 0<w i}
    Nonempty κ ∧ (∑ i:κ,w i=1) ∧
      (∑ i:κ,w i • p i=∑ i,w i • p i) ∧
      ∀ f : ι → ℝ,∑ i:κ,w i*f i=∑ i,w i*f i := by
  classical
  dsimp only
  have he (f : ι → E) : (∑ i:{i : ι // 0<w i},w i • f i)=∑ i,w i • f i := by
    rw [←Finset.sum_subtype (p := fun i=>0<w i) (Finset.univ.filter (fun i=>0<w i)) (by simp) (fun i=>w i • f i)]
    exact Finset.sum_subset (Finset.filter_subset _ _) (by
      intro i hi hn
      have hi0 : w i=0 := le_antisymm (not_lt.mp (by simpa using hn)) (hw i)
      simp only [hi0,zero_smul])
  have hr (f : ι → ℝ) : (∑ i:{i : ι // 0<w i},w i*f i)=∑ i,w i*f i := by
    rw [←Finset.sum_subtype (p := fun i=>0<w i) (Finset.univ.filter (fun i=>0<w i)) (by simp) (fun i=>w i*f i)]
    exact Finset.sum_subset (Finset.filter_subset _ _) (by
      intro i hi hn
      have hi0 : w i=0 := le_antisymm (not_lt.mp (by simpa using hn)) (hw i)
      simp only [hi0,zero_mul])
  have hsum : (∑ i:{i : ι // 0<w i},w i)=1 := by
    simpa only [mul_one] using (hr (fun _=>1)).trans (by simpa only [mul_one] using hs)
  refine ⟨?_,hsum,he p,hr⟩
  by_contra hn
  have : IsEmpty {i : ι // 0<w i} := not_nonempty_iff.mp hn
  simp at hsum

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartParameter
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ChartParameter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma MaximumRow.parameter_nonnegative {v : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {z : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    {ι : Type} [Fintype ι] (pj : ι → TangentSpace 𝓘(ℝ,Model n) R.q.1.1) (w : ι → ℝ)
    (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) (hb : ∑ i,w i • pj i=R.q.1.2)
    (ha : ∀ i,pj i∈activeLogs (modifiedDatum v α D b Bo) R.q.1.1) :
    1/4096+4*b/bplus≤Bc ((v (riemannianExp R.q.1.1 R.q.1.2)-α)/D)-
      ∑ i,w i*Bo ((v (riemannianExp R.q.1.1 (pj i))-α)/D) := by
  classical
  let κ := {i : ι // 0<w i}
  have H := positive_barycentric_restriction pj w hw hs
  let : Nonempty κ := H.1
  have HP := R.parameter κ (fun i=>pj i) (fun i=>w i) (fun i=>i.2)
    H.2.1 (H.2.2.1.trans hb) (fun i=>ha i)
  rw [H.2.2.2 (fun i=>Bo ((v (riemannianExp R.q.1.1 (pj i))-α)/D))] at HP
  exact HP

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma MaximumRow.chart_first_limit_parameter {v G : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {a z : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    (ha : R.q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source)
    {q : ℕ → subgradientGraph (n := n) (cTransform (modifiedDatum v α D b Bo))}
    (J : ChartFixedPrefixLimit a (modifiedDatum v α D b Bo) G t q R.q) :
    let x := graphBaseCoordinate a R.q.1
    1/4096+4*b/bplus≤Bc ((v (movingNormal a (x,graphVelocityCoordinate a R.q.1))-α)/D)-
      ∑ i,J.w₀ i*Bo ((v (movingNormal a (x,J.pj₀ i))-α)/D) := by
  let x := graphBaseCoordinate a R.q.1
  let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ R.q.1.1
  have hre := graph_coordinate_reconstruction ha
  have hbase : (extChartAt 𝓘(ℝ,Model n) a).symm x=R.q.1.1 :=
    congrArg Bundle.TotalSpace.proj hre
  have hvel : A (graphVelocityCoordinate a R.q.1)=R.q.1.2 := by
    have H := congrArg (fun w:TangentBundle 𝓘(ℝ,Model n) M=>show Model n from w.2) hre
    change chartFiberInverse a x (graphVelocityCoordinate a R.q.1)=R.q.1.2 at H
    unfold chartFiberInverse at H
    rw [hbase] at H
    exact H
  let pj : Fin (Module.finrank ℝ (Model n)+1) → TangentSpace 𝓘(ℝ,Model n) R.q.1.1 :=
    fun i=>A (J.pj₀ i)
  have hbar : ∑ i,J.w₀ i • pj i=R.q.1.2 := by
    calc
      _=A (∑ i,J.w₀ i • J.pj₀ i) := by simp [pj]
      _=R.q.1.2 := by rw [J.baryLimit]; exact hvel
  have hactive : ∀ i,pj i∈activeLogs (modifiedDatum v α D b Bo) R.q.1.1 := by
    intro i
    have HH := J.activeLimit i
    change chartFiberInverse a x (J.pj₀ i)∈activeLogs _ ((extChartAt 𝓘(ℝ,Model n) a).symm x) at HH
    unfold chartFiberInverse at HH
    rw [hbase] at HH
    exact HH
  have HP := R.parameter_nonnegative pj J.w₀ J.nonnegLimit J.totalLimit hbar hactive
  have hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target := (extChartAt 𝓘(ℝ,Model n) a).map_source ha
  have he (p : Model n) : movingNormal a (x,p)=riemannianExp R.q.1.1 (A p) := by
    rw [movingNormal_eq hx,hbase]
  change 1/4096+4*b/bplus≤Bc ((v (movingNormal a (x,graphVelocityCoordinate a R.q.1))-α)/D)-
      ∑ i,J.w₀ i*Bo ((v (movingNormal a (x,J.pj₀ i))-α)/D)
  simp only [he,hvel]
  exact HP

end ChartParameter
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_EigenOrder
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Module
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

lemma bilinearOperator_symmetric {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ v w:E, B v w=B w v) : (bilinearOperator B).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (bilinearOperator B v) w=inner ℝ v (bilinearOperator B w)
  calc
    _=B v w := bilinearOperator_inner B v w
    _=B w v := hB v w
    _=inner ℝ (bilinearOperator B w) v := (bilinearOperator_inner B w v).symm
    _=inner ℝ v (bilinearOperator B w) := real_inner_comm _ _

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_InverseProfile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Module
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

lemma symmetric_eigenvalue_pos {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (hn : finrank ℝ E=n) (hpos : ∀ x:E, x≠0 → 0 < inner ℝ (A x) x) (i:Fin n) :
    0 < hA.eigenvalues hn i := by
  have H := hpos (hA.eigenvectorBasis hn i) ((hA.eigenvectorBasis hn).toBasis.ne_zero i)
  rw [hA.apply_eigenvectorBasis,real_inner_smul_left,real_inner_self_eq_norm_sq,
    (hA.eigenvectorBasis hn).norm_eq_one] at H
  simpa using H
end WeakMTWTransport

end



end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FrameDet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section FrameDet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.frameDetFinite
attribute [local instance] OAI.WeakMTWTransport.frameDetComplete
omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma frameNormDet_pos {a:M} {b:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    0<(chartFiberInverse a b).toLinearMap.normDet := by
  apply lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm _)
  intro h
  exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp h)
    (LinearMap.ker_eq_bot.mpr (chartFiberInverse_injective hb))

end FrameDet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_FrameDeterminantClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section FrameDeterminantClosure
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.frame_determinant_closure (hmtw:WeakMTW (n:=n) (M:=M))
    {μ κ A χ K:ℝ} (hμ:0 < μ) (hκ:0 < κ) (hA:0 < A) (hχ:0 < χ) (hK:0 < K) :
    ∃B:ℝ,0 < B ∧ ∀(ι:Type) [Fintype ι] (a c:M)
      (r:ι → TangentSpace 𝓘(ℝ,Model n) a) (m:ι → ℝ) (q:TangentSpace 𝓘(ℝ,Model n) a),
      (∀j,0 ≤ m j) → (∑j,m j=1) → (∀j,r j∈minimizingVectors a) →
      (∑j,m j • r j=q) → ∀i (e:TangentSpace 𝓘(ℝ,Model n) a) (t D l lo:ℝ),
      μ ≤ m i → ‖e‖=1 → 0 < t → 0 < D → 0 < inner ℝ q e →
      κ*D ≤ (inner ℝ q e)^2 → ‖r i‖^2-‖q‖^2 ≤ A*D → r i=q+t • e →
      l∈Icc (1/2:ℝ) 1 → l<1 → lo∈Icc (1:ℝ) 2 → 1 < lo →
      ∀rc:TangentSpace 𝓘(ℝ,Model n) c,rc∈minimizingVectors c →
      reverseRay (⟨c,l • rc⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ →
      ∀V W X:ℝ,0 < W → 0 < X →
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ ≤ expJacobian c rc*V →
      expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
        (lo⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*W ≤
        (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*lo^n*K*
          (expJacobian a (r i))^2 →
      X*V ≤ W → X ≤ B := by
  have hc0:0 < (1/2:ℝ)^n*χ:=mul_pos (by positivity) hχ
  have hC0:0 < (2:ℝ)^n*K:=mul_pos (by positivity) hK
  obtain ⟨B,hB,HB⟩:=hmtw.uniform_three_determinant_closure hμ hκ hA hc0
    (show (0:ℝ)<1 by norm_num) hC0
  refine ⟨B,hB,?_⟩
  intro ι _ a c r m q hmn hmt hr hbar i e t D l lo hmi he ht hD hqe hqD hgap hri
    hl hl1 hlo hlo1 rc hrc hrev V W X hW hX hdc hdo hXdet
  have hl0:0 < l:=lt_of_lt_of_le (by norm_num) hl.1
  have hlo0:0 < lo:=zero_lt_one.trans hlo1
  have hrev':reverseRay (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨c,l • rc⟩:=by
    rw [←hrev,reverseRay_reverseRay]
  have hcontract:=contracted_minimizer_mem_injectivityDomain hrc hl0 hl1
  have hqID:q∈injectivityDomain a:=by
    have H:=reverseRay_injectivityDomain (z:=⟨c,l • rc⟩) hcontract
    rwa [hrev] at H
  have hσ:=expJacobian_pos_of_injectivityDomain hqID
  have hσti:0 < expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
      (lo⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2):=by
    apply expJacobian_pos_of_injectivityDomain
    exact contracted_minimizer_mem_injectivityDomain (reverseRay_minimizing (hr i))
      (inv_pos.mpr hlo0) ((inv_lt_one₀ hlo0).mpr hlo1)
  let f:ℝ:=(chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2
  have hf:0 < f:=sq_pos_of_pos (frameNormDet_pos (mem_extChartAt_target a))
  have hlpow:(1/2:ℝ)^n ≤ l^n:=pow_le_pow_left₀ (by norm_num) hl.1 n
  have hlopow:lo^n ≤ (2:ℝ)^n:=pow_le_pow_left₀ hlo0.le hlo.2 n
  have hσc:0 < expJacobian c rc:=by
    have hp:0 < f*l^n*(expJacobian a q)^2*χ:=by positivity
    have hV:0 < expJacobian c rc*V:=hp.trans_le hdc
    exact lt_of_le_of_ne (expJacobian_nonneg c rc) (by
      intro hzero
      rw [←hzero,zero_mul] at hV
      exact (lt_irrefl (0:ℝ)) hV)
  have hσi:0 < expJacobian a (r i):=by
    have hp:0 < expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
      (lo⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*W:=mul_pos hσti hW
    have H:=hp.trans_le hdo
    exact lt_of_le_of_ne (expJacobian_nonneg a (r i)) (by
      intro hz
      rw [←hz,zero_pow (by decide),mul_zero] at H
      exact (lt_irrefl (0:ℝ)) H)
  have hlow:((1/2:ℝ)^n*χ)*(expJacobian a q)^2/expJacobian c rc ≤ V/f:=by
    apply (div_le_div_iff₀ hσc hf).mpr
    have H:=mul_le_mul_of_nonneg_right hlpow
      (show 0 ≤ f*(expJacobian a q)^2*χ by positivity)
    dsimp only [f] at H
    nlinarith only [H,hdc]
  have hupper:W/f≤((2:ℝ)^n*K)*(expJacobian a (r i))^2/
      expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
        (lo⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2):=by
    apply (div_le_div_iff₀ hf hσti).mpr
    have H:=mul_le_mul_of_nonneg_right hlopow
      (show 0 ≤ f*K*(expJacobian a (r i))^2 by positivity)
    dsimp only [f] at H
    nlinarith only [H,hdo]
  have hratio:(1:ℝ)*X*(V/f)≤W/f:=by
    rw [one_mul,←mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hf).mpr hXdet
  refine HB ι a r m q hmn hmt hr hbar.symm i e t D hmi he ht hD hqe hqD hgap hri l hl lo hlo
    ?_ hσ hσi ?_ hσti (V/f) (W/f) X hX ?_ hupper hratio
  · rw [hrev']
    simpa only [smul_smul,inv_mul_cancel₀ hl0.ne',one_smul] using hrc
  · rw [hrev']
    simpa only [smul_smul,inv_mul_cancel₀ hl0.ne',one_smul] using hσc
  · rw [hrev']
    simpa only [smul_smul,inv_mul_cancel₀ hl0.ne',one_smul] using hlow

end FrameDeterminantClosure
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SectionOscillation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

variable [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
lemma densityDualClass_isDual {vol : Measure M} {lam cap : ℝ} {x0 : M}
    {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)} (h : uv ∈ densityDualClass vol lam cap x0) :
    IsCostDualPair uv.1 uv.2 := by
  constructor
  · exact congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.1.2.1.symm
  · exact congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.1.2.2.symm

end SectionOscillation

open Filter

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumFamily.compact_subseq {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo) :
    ∃ σ:ℕ → ℕ,StrictMono σ ∧ ∃ β∈Icc bminus bplus,
      ∃ Q:TangentBundle 𝓘(ℝ,Model n) M,Q.2∈minimizingVectors Q.1 ∧
        Tendsto (F.b ∘ σ) atTop (𝓝 β) ∧
        Tendsto (fun k=>(F.row (σ k)).q.1) atTop (𝓝 Q) := by
  let : FirstCountableTopology (ModelProd (Model n) (Model n)) :=
    inferInstanceAs (FirstCountableTopology (Model n×Model n))
  let : FirstCountableTopology (TangentBundle 𝓘(ℝ,Model n) M) := by
    constructor
    intro x
    let e := chartAt (ModelProd (Model n) (Model n)) x
    have he : map e.symm (𝓝 (e x))=𝓝 x := e.symm_map_nhds_eq (mem_chart_source _ _)
    rw [←he]
    infer_instance
  have hc := isCompact_Icc (a := bminus) (b := bplus) |>.prod
    (isCompact_total_minimizingVectors (n := n) (M := M))
  obtain ⟨q,hq,σ,hσ,hlim⟩ := hc.isSeqCompact (fun k=>
    show (F.b k,(F.row k).q.1)∈Icc bminus bplus×ˢ
      {Q:TangentBundle 𝓘(ℝ,Model n) M | Q.2∈minimizingVectors Q.1} from
        ⟨Ioo_subset_Icc_self (F.parameter k),(F.row k).minimizing⟩)
  exact ⟨σ,hσ,q.1,hq.1,q.2,hq.2,hlim.fst_nhds,hlim.snd_nhds⟩

lemma MaximumFamily.limit_coordinates {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo)
    {Q:TangentBundle 𝓘(ℝ,Model n) M}
    (hQ : Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 Q)) :
    Tendsto (fun k=>graphBaseCoordinate Q.1 (F.row k).q.1) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) Q.1 Q.1)) ∧
    Tendsto (fun k=>graphVelocityCoordinate Q.1 (F.row k).q.1) atTop (𝓝 (show Model n from Q.2)) ∧
    Tendsto F.z atTop (𝓝 (riemannianExp Q.1 Q.2)) ∧
    Tendsto (fun k=>riemannianExp (F.row k).q.1.1 (F.row k).q.1.2) atTop
      (𝓝 (riemannianExp Q.1 Q.2)) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (⟨Q.1,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hs : Q∈χ.source := (tangent_chart_source_iff _ _).mpr (mem_extChartAt_source Q.1)
  have HC := ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds hs)).tendsto.comp hQ
  have hvel : Tendsto (fun k=>graphVelocityCoordinate Q.1 (F.row k).q.1) atTop
      (𝓝 (graphVelocityCoordinate Q.1 Q)) := HC.snd_nhds
  rw [graph_coordinates_at_center] at hvel
  have HE := contMDiff_riemannianExp.continuous.tendsto Q |>.comp hQ
  have HP := (contMDiff_riemannianExp.continuous.comp contMDiff_tangentScale.continuous).tendsto (1,Q)
    |>.comp (F.time.prodMk_nhds hQ)
  have HZ : Tendsto F.z atTop (𝓝 (riemannianExp Q.1 Q.2)) := by
    change Tendsto (fun k=>riemannianExp (F.row k).q.1.1 (F.t k • (F.row k).q.1.2)) atTop
      (𝓝 (riemannianExp Q.1 ((1:ℝ) • Q.2))) at HP
    simp only [one_smul] at HP
    exact HP.congr (fun k=>(F.row k).projection)
  exact ⟨HC.fst_nhds,hvel,HZ,HE⟩
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumCenterSign
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumCenterSign
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumJensenFamily.center_parameter_bound
    {hmtw:WeakMTW (n:=n) (M:=M)} {v:M → ℝ} {hv:Continuous v}
    {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    (hm:0 ≤ bminus) (hp:0 < bplus) (hb:∀s,0 ≤ Bo s) (k:ℕ) :
    (1:ℝ)/4096 ≤ Bc ((v (riemannianExp (F.row k).q.1.1 (F.row k).q.1.2)-α)/D) := by
  have H:=(F.row k).chart_first_limit_parameter (J.poleSource k) (J.first k)
  dsimp only at H
  have hs:0 ≤ ∑i,(J.first k).w₀ i*Bo ((v (movingNormal a
      (graphBaseCoordinate a (F.row k).q.1,(J.first k).pj₀ i))-α)/D) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg ((J.first k).nonnegLimit i) (hb _)
  have hp':0 ≤ 4*F.b k/bplus:=div_nonneg (mul_nonneg (by norm_num)
    (hm.trans (F.parameter k).1.le)) hp.le
  have hbt:graphBaseCoordinate a (F.row k).q.1∈(extChartAt 𝓘(ℝ,Model n) a).target:=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (J.poleSource k)
  have heq:movingNormal a (graphBaseCoordinate a (F.row k).q.1,
      graphVelocityCoordinate a (F.row k).q.1)=riemannianExp (F.row k).q.1.1 (F.row k).q.1.2 := by
    rw [movingNormal_eq hbt]
    exact congrArg (fun z:TangentBundle 𝓘(ℝ,Model n) M=>riemannianExp z.1 z.2)
      (graph_coordinate_reconstruction (J.poleSource k))
  rw [heq] at H
  linarith only [H,hs,hp']

lemma MaximumJensenFamily.center_limit_positive
    {hmtw:WeakMTW (n:=n) (M:=M)} {v:M → ℝ} {hv:Continuous v}
    {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    (hm:0 ≤ bminus) (hp:0 < bplus) (hb:∀s,0 ≤ Bo s) (hc:Continuous Bc)
    {q:Model n} (he:riemannianExp a q=c)
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M))) :
    (1:ℝ)/4096 ≤ Bc ((v c-α)/D) := by
  have H:=(F.limit_coordinates hQ).2.2.2
  rw [he] at H
  exact ge_of_tendsto (hc.continuousAt.tendsto.comp
    (((hv.continuousAt.tendsto.comp H).sub_const α).div_const D))
    (Eventually.of_forall (J.center_parameter_bound hm hp hb))

end MaximumCenterSign
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_PullbackDet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
open scoped Topology

namespace WeakMTWTransport
section PullbackDet
variable {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace E] in
lemma symmetric_det_pos {A:E →L[ℝ] E}
    (hA:∀x y,inner ℝ (A x) y=inner ℝ x (A y))
    (hp:∀x,x≠0 → 0 < inner ℝ (A x) x) : 0<A.det := by
  have hs:A.toLinearMap.IsSymmetric:=hA
  change 0<A.toLinearMap.det
  rw [hs.det_eq_prod_eigenvalues rfl]
  exact Finset.prod_pos (fun i _=>symmetric_eigenvalue_pos hs rfl hp i)

end PullbackDet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OuterTemplatePrimitive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma centerTemplate_le_outer {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta)
    (heta1 : eta ≤ 1/128) (hetasmall : eta ≤ templateEps/(24*(128*(M0+3)*(K+1)))) :
    centerTemplate s ≤ outerTemplate M0 K eta s := by
  by_cases hs : s ≤ 1-eta
  · exact (centerTemplate_bounds s).2.le.trans (outerTemplate_lower hM hK heta heta1 hetasmall hs)
  · exact (centerTemplate_right (by linarith only [hs,heta1])).le.trans
      (outerTemplate_nonneg hM hK heta heta1 hetasmall)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumTemplateBound
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
section MaximumTemplateBound
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance templateDualGroup_ref9b91_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance templateDualSpace_ref9b91_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance templateBilinearGroup_ref9b91_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance templateBilinearSpace_ref9b91_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma WeakMTW.maximum_template_bound_oai (hmtw:WeakMTW (n:=n) (M:=M))
    (hn:0 < n) {lam cap:ℝ} (hlam:0 < lam) (hcap:lam ≤ cap) :
    ∃B:ℝ,0 < B ∧ ∃eps:ℝ,0 < eps ∧
    ∀K eta:ℝ,1 ≤ K → 0 < eta → eta ≤ 1/128 →
    (let M0:ℝ:=12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)
     eta ≤ templateEps/(24*(128*(M0+3)*(K+1)))) →
    ∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),uv∈densityDualClass (metricVolume n) lam cap x0 →
    ∀α D bm bp:ℝ,0 < D → 0 < bm → 0 < bp →
    bp/D*centerGamma ≤ 1 → bp/D*centerGamma/2 < eps →
    ∀C:ℝ,0 ≤ C →
      (∀s,|deriv (outerTemplate (12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)) K eta) s| ≤ C) →
      bp/D*C ≤ 1/2 →
    (∀z:M,sectionOscillation uv.1 uv.2 z
      ((2*(12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096))+10)*bp) ≤ (1+eta)*D) →
    2*(2*(12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096))+10)*bp ≤ eta*D →
    MaximumFamily (n:=n) uv.2 α D bm bp centerTemplate
      (outerTemplate (12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)) K eta) →
    (((1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ)))^(n-1)*K/(8*centerGamma^2)) ≤ B := by
  classical
  have hgamma:=centerGamma_pos
  obtain ⟨c0,hc0,HG⟩:=exists_maximum_center_gain (n:=n) (M:=M)
  obtain ⟨χ,hχ,Hχ⟩:=exists_density_original_center_good (n:=n) (M:=M) hlam hcap
  obtain ⟨δ,hδ,Kd,hKd,U,hU,hU1,HS⟩:=hmtw.exists_maximum_simultaneous hn hlam (hlam.le.trans hcap)
  let a0:ℝ:=c0/(16*centerGamma)
  let μ:ℝ:=(1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ))
  have ha0:0 < a0:=by dsimp [a0] <;> positivity
  have hμ:0 < μ:=by dsimp [μ] <;> positivity
  obtain ⟨B,hB,HB⟩:=hmtw.frame_determinant_closure hμ ha0
    (show 0 < 3+9/(4*a0) by positivity) hχ hKd
  obtain ⟨eps,heps,HE⟩:=Metric.mem_nhds_iff.mp (Filter.Eventually.and (show ∀ᶠ l in 𝓝 (1:ℝ), l∈U from hU.mem_nhds hU1) HG)
  refine ⟨B,hB,eps,heps,?_⟩
  intro K eta hK heta heta1 hetasmall x0 uv huv α D bm bp hD hbm hbp hcenter hclose C hC hder houter hosc herror F
  let M0:ℝ:=12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)
  let Bo:=outerTemplate M0 K eta
  let H:ℝ:=2*M0+8
  have hM:2 ≤ M0:=by dsimp [M0]; have hn0:=Nat.cast_nonneg (α:=ℝ) (Module.finrank ℝ (Model n)); linarith
  have hBo:ContDiff ℝ ∞ Bo:=outerTemplate_smooth _ _ _
  have hob (s):0 ≤ Bo s ∧ Bo s ≤ H:=⟨outerTemplate_nonneg hM hK heta heta1 hetasmall,
    outerTemplate_upper hM hK heta heta1 hetasmall⟩
  have hprof (s):centerTemplate s ≤ Bo s:=centerTemplate_le_outer hM hK heta heta1 hetasmall
  have hd:=densityDualClass_isDual huv
  let Lv:ℝ≥0:=⟨Metric.diam (univ:Set M),Metric.diam_nonneg⟩
  have hv:LipschitzWith Lv (uv.2:M → ℝ):=by
    rw [hd.2]
    exact cTransform_lipschitz uv.1.continuous (fun x y=>Metric.dist_le_diam_of_mem
      isCompact_univ.isBounded (mem_univ x) (mem_univ y))
  obtain ⟨A0,hA0⟩:=isCompact_univ.exists_bound_of_continuousOn uv.2.continuous.continuousOn
  have hrange:∀y:M,uv.2 y∈Icc (-A0) A0:=fun y=>abs_le.mp (hA0 y (mem_univ y))
  have hcsmall (b:ℝ) (hb:b∈Icc bm bp): b/D*(centerGamma/2) ≤ 1/2:=by
    have ht:=mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hD).mpr hb.2) centerGamma_pos.le
    nlinarith only [ht,hcenter]
  have hosmall (b:ℝ) (hb:b∈Icc bm bp):b/D*C ≤ 1/2:=
    (mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hD).mpr hb.2) hC).trans houter
  have hmono (b:ℝ) (hb:b∈Icc bm bp):Monotone (fun s=>modifiedScalar α D centerTemplate (b,s)):=
    (modifiedScalar_strictMono centerTemplate_smooth (by positivity) hD (hbm.le.trans hb.1)
      (hcsmall b hb) exact_center_deriv_abs α).monotone
  have hmonoO (b:ℝ) (hb:b∈Icc bm bp):StrictMono (fun s=>modifiedScalar α D Bo (b,s)):=
    modifiedScalar_strictMono hBo hC hD (hbm.le.trans hb.1) (hosmall b hb) hder α
  have hLipφ (b:ℝ) (hb:b∈Icc bm bp):LipschitzWith 2 (fun s=>modifiedScalar α D centerTemplate (b,s)):=
    modifiedScalar_lipschitz centerTemplate_smooth (by positivity) hD (hbm.le.trans hb.1)
      (hcsmall b hb) exact_center_deriv_abs α
  have hLip (b:ℝ) (hb:b∈Icc bm bp):LipschitzWith (2*Lv) (modifiedDatum uv.2 α D b centerTemplate):=
    (hLipφ b hb).comp hv
  have hslope (b:ℝ) (hb:b∈Icc bm bp) (y:M):
      0 < deriv (fun s=>modifiedScalar α D centerTemplate (b,s)) (uv.2 y) ∧
      deriv (fun s=>modifiedScalar α D centerTemplate (b,s)) (uv.2 y)<1:=by
    refine ⟨lt_of_lt_of_le (by norm_num)
      (modifiedScalar_slope_bounds centerTemplate_smooth (by positivity) hD (hbm.le.trans hb.1)
        (hcsmall b hb) exact_center_deriv_abs α (uv.2 y)).1,?_⟩
    rw [modifiedScalar_deriv centerTemplate_smooth]
    have H:=mul_neg_of_pos_of_neg (div_pos (hbm.trans_le hb.1) hD) (centerTemplate_deriv_neg ((uv.2 y-α)/D))
    linarith only [H]
  obtain ⟨σ,hσ,β,hβmem,Q,hq,hβ,hQ⟩:=F.compact_subseq
  let F1:=F.comp σ hσ.tendsto_atTop
  let a:=Q.1
  let q:Model n:=Q.2
  let c:=riemannianExp a q
  obtain ⟨r0,hr0,N,hN,hNt,hgood⟩:=original_chart_good_null (Hχ x0 uv huv) uv.1.continuous hd c
  obtain ⟨k0,⟨J⟩⟩:=F1.eventually_jensen_first hmtw uv.1.continuous uv.2.continuous hd hBo.continuous
    (modifiedScalar_contDiff centerTemplate_smooth α D) hmono hLipφ hrange hQ hN
  let τ:ℕ → ℕ:=fun k=>k+k0
  have hτ:Tendsto τ atTop atTop:=tendsto_add_atTop_nat k0
  let F2:=F1.comp τ hτ
  have hQ2:Tendsto (fun k=>(F2.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)):=hQ.comp hτ
  have hβ2:Tendsto F2.b atTop (𝓝 β):=hβ.comp hτ
  let l:=deriv (fun s=>modifiedScalar α D centerTemplate (β,s)) (uv.2 c)
  let kc:=iteratedDeriv 2 (fun s=>modifiedScalar α D centerTemplate (β,s)) (uv.2 c)
  have hjcenter:=J.center_limit_positive hbm.le hbp (fun s=>(hob s).1) centerTemplate_smooth.continuous rfl hQ2
  have hcentβ:β/D*centerGamma ≤ 1:=
    (mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hD).mpr hβmem.2) centerGamma_pos.le).trans hcenter
  obtain ⟨hlhalf,hl1,hkc,hkc1,hkc2⟩:=exact_center_slope_curvature hD (hbm.trans_le hβmem.1) hcentβ
    (lt_of_lt_of_le (by norm_num) hjcenter)
  change -kc / l^2 ≤ 4*centerGamma*(1-l)/D at hkc2
  have hl:0 < l:=lt_of_lt_of_le (by norm_num) hlhalf
  have hldist:dist l 1 < eps:=by
    rw [Real.dist_eq]
    apply exact_center_slope_small hD (hbm.le.trans hβmem.1)
    have h:=mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hD).mpr hβmem.2) centerGamma_pos.le
    exact (div_le_div_of_nonneg_right h (by norm_num)).trans_lt hclose
  obtain ⟨hlU,hgain⟩:=HE (show l∈ball 1 eps from hldist)
  have hH:=hgain hl hl1 hmtw uv.1 uv.2 uv.1.continuous Lv hv hd α D bm bp centerTemplate Bo
    hBo.continuous centerTemplate_smooth hmono (2*Lv) hLip F2 a c N J q β hq rfl hQ2 hβ2 rfl
  have hqa:2*(-(kc/l^2))*a0*D ≤ c0*(1-l):=by
    have H:=mul_le_mul_of_nonneg_right hkc2 (show 0 ≤ 2*a0*D by positivity)
    have he:(4*centerGamma*(1-l)/D)*(2*a0*D)=c0*(1-l)/2:=by
      dsimp only [a0]
      field_simp [hD.ne', centerGamma_pos.ne']
      ring
    rw [he] at H
    have hpos:0 ≤ c0*(1-l):=mul_nonneg hc0.le (sub_nonneg.mpr hl1.le)
    calc
      2*(-(kc/l^2))*a0*D = (-kc/l^2)*(2*a0*D) := by ring
      _ ≤ c0*(1-l)/2 := H
      _ ≤ c0*(1-l) := by linarith only [hpos]
  have hmargin (s:ℝ) (hs:-2*eta ≤ s) (hs':s ≤ 1-eta) (hsM:Bo s ≤ M0):
      1 < deriv (fun z=>modifiedScalar α D Bo (β,z)) (α+D*s) ∧
      iteratedDeriv 2 (fun z=>modifiedScalar α D Bo (β,z)) (α+D*s)<0:=by
    have he:(α+D*s-α)/D=s:=by field_simp [hD.ne'] <;> ring
    have hh:=exact_outer_slope_curvature hM hK heta hD (hbm.trans_le hβmem.1) hC hder
      (hosmall β hβmem) (by rwa [he]) (by rwa [he]) (by rwa [he])
    exact ⟨hh.1,hh.2.2.1⟩
  have hHeq:H+2=2*M0+10:=by dsimp [H] <;> ring
  have herr (k):2*(H+2)*F2.b k ≤ eta*D:=by
    have hh:=mul_le_mul_of_nonneg_left (F2.parameter k).2.le (show 0 ≤ 2*(H+2) by dsimp [H,M0] <;> positivity)
    apply hh.trans
    simpa only [hHeq] using herror
  have hbk (k):0 < F2.b k:=hbm.trans (F2.parameter k).1
  have hosc2 (k):sectionOscillation uv.1 uv.2 (F2.row k).q.1.1 ((H+2)*F2.b k) ≤ (1+eta)*D:=by
    apply le_trans (sectionOscillation_mono uv.2.continuous hd _ (by have hb:=hbk k; dsimp [H,M0] <;> positivity)
      (mul_le_mul_of_nonneg_left (F2.parameter k).2.le (show 0 ≤ H+2 by dsimp [H,M0] <;> positivity)))
    simpa only [hHeq] using hosc (F2.row k).q.1.1
  obtain ⟨s,hs,r,m,L,CL,hCL,i,hr,hm,hL,hCLbd,hri,hmn,hmt,hbar,hmi,hsl,hsu,hcapO,e,t,he,ht,hriq,hqe,hqD,hgap⟩:=
    J.selected_pole_compact hlam (hlam.le.trans hcap) huv hBo hd hbm.le hbp hprof hob
      (fun s=>⟨(centerTemplate_bounds s).1.le,(centerTemplate_bounds s).2.le⟩)
      (fun s hs=>(centerTemplate_right hs).le) hβ2 hQ2
      (mul_pos hc0 (sub_pos.mpr hl1)) (div_neg_of_neg_of_pos hkc (sq_pos_of_pos hl)) hH
      hD ha0 hqa heta1 le_rfl le_rfl (by linarith only [heta1])
      (fun s hs=>outerTemplate_lower hM hK heta heta1 hetasmall hs.le) herr hosc2 hmonoO hmargin
  let J3:=J.comp s hs.tendsto_atTop
  let F3:=F2.comp s hs.tendsto_atTop
  obtain ⟨CH,hCH,hCHbd⟩:=eventual_lower_bound_of_center_gain (mul_pos hc0 (sub_pos.mpr hl1)).le
    (div_neg_of_neg_of_pos hkc (sq_pos_of_pos hl)).le hH
  let lo:=deriv (fun z=>modifiedScalar α D Bo (β,z)) (uv.2 (riemannianExp a (r i)))
  let ko:=iteratedDeriv 2 (fun z=>modifiedScalar α D Bo (β,z)) (uv.2 (riemannianExp a (r i)))
  obtain ⟨hlo,hlo2,hko,hko1⟩:=exact_outer_slope_curvature hM hK heta hD
    (hbm.trans_le hβmem.1) hC hder (hosmall β hβmem) hsl hsu hcapO
  obtain ⟨rc,hrc,hrev,V,W,hVs,hVp,hWs,hWp,hσc,hdc,hdo,hdet⟩:=HS x0 uv huv Lv hv hd α D bm bp
    (-A0) A0 centerTemplate Bo hBo.continuous centerTemplate_smooth hBo hmono hmonoO hrange hslope
    (2*Lv) hLip F3 a c χ N r0 hχ hr0 hgood J3 q β l kc hq rfl
    (hQ2.comp hs.tendsto_atTop) (hβ2.comp hs.tendsto_atTop) rfl rfl hlU hl hl1 hkc
    r m L hr hm hL CH CL hCH hCL (hs.tendsto_atTop.eventually hCHbd) hCLbd i (hri i)
    (hμ.trans_le hmi) e t lo ko he ht hriq hqe rfl rfl hlo hko
  have hVdet:0 < (bilinearOperator V).det:=symmetric_det_pos (bilinearOperator_symmetric hVs) (by
    intro d hd; simpa only [bilinearOperator_inner] using hVp d hd)
  have hWdet:0 < (bilinearOperator W).det:=symmetric_det_pos (bilinearOperator_symmetric hWs) (by
    intro d hd; simpa only [bilinearOperator_inner] using hWp d hd)
  have hgainDet:=scalar_determinant_gain hμ hmi (zero_lt_one.trans_le hK) centerGamma_pos
    (hbm.trans_le hβmem.1) hD hVdet.le hWdet.le hkc1 hko1 hdet
  exact HB _ a c (fun j=>(show TangentSpace 𝓘(ℝ,Model n) a from r j)) m q hmn hmt hri hbar
    i e t D l lo hmi he ht hD hqe hqD hgap hriq ⟨hlhalf,hl1.le⟩ hl1 ⟨hlo.le,hlo2⟩ hlo rc hrc hrev
    (bilinearOperator V).det (bilinearOperator W).det (μ^(n-1)*K/(8*centerGamma^2)) hWdet
    (by positivity) hdc hdo hgainDet

end MaximumTemplateBound
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.maximum_template_bound_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.maximum_template_bound_oai.{u_1}
