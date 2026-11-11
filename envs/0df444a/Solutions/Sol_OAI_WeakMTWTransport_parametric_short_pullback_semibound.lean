-- Prove2me | solution 1 for OAI.WeakMTWTransport.parametric_short_pullback_semibound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T18:51:39.140903+00:00
-- url     : https://prove2.me/submissions/db6f7b07-9d90-4f4c-a41d-c856d7f9a4a7

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
import Definitions.Def_OAIQ232A004
import Definitions.Def_OAIQ232A012
import Theorems.Thm_OAI_WeakMTWTransport_exists_parametric_short_lower_sequence

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_FullSet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma HasSecondTaylor.eventually {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ h in 𝓝 (0:E), |f h-f 0-l h-B h h/2|≤ε*‖h‖^2 := by
  simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using hf.def hε

lemma hasSecondTaylor_of_contDiffAt {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    HasSecondTaylor f (fderiv ℝ f 0) (fderiv ℝ (fderiv ℝ f) 0) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hn := hf.eventually (by norm_num)
  have hD := ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right
    (m := 0) (by norm_num)).continuousAt
  have he : ∀ᶠ z : E in 𝓝 0,
      ‖fderiv ℝ (fderiv ℝ f) z-fderiv ℝ (fderiv ℝ f) 0‖<ε := by
    exact Metric.tendsto_nhds.mp hD ε hε |>.mono (fun _ h => by simpa only [dist_eq_norm] using h)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (hn.and he)
  filter_upwards [Metric.ball_mem_nhds (0:E) hr] with h hh
  have H := second_order_remainder_bound_on_ball hr hε.le
    (fun z hz => (hball hz).1) (fun z hz => (hball hz).2.le) hh
  simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using H

lemma HasSecondTaylor.sub {f g : E → ℝ} {l k : E →L[ℝ] ℝ}
    {B C : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B)
    (hg : HasSecondTaylor g k C) : HasSecondTaylor (fun h => f h-g h) (l-k) (B-C) := by
  unfold HasSecondTaylor at *
  have he : (fun h => (f h-g h)-(f 0-g 0)-(l-k) h-(B-C) h h/2) =
      (fun h => (f h-f 0-l h-B h h/2)-(g h-g 0-k h-C h h/2)) := by
    funext h
    simp only [_root_.sub_apply]
    ring
  rw [he]
  exact Asymptotics.IsLittleO.sub hf hg

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SecondDerivativeTaylor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasSecondTaylor_of_second_derivative {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {x : E} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hD : HasFDerivAt f' B x) :
    HasSecondTaylor (fun h => f (x+h)) (f' x) B := by
  have hs : ∀ v w, B v w=B w v := second_derivative_symmetric_of_eventually hf hD
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hrem := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hD).def hε
  have hnear : ∀ᶠ h : E in 𝓝 0, HasFDerivAt f (f' (x+h)) (x+h) := by
    exact (show ContinuousAt (fun h : E => x+h) 0 from continuousAt_const.add continuousAt_id).eventually
      (by simpa only [add_zero] using hf)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (hnear.and hrem)
  let R : E → ℝ := fun h => f (x+h)-f x-f' x h-B h h/2
  have hR0 : R 0=0 := by simp [R]
  have hdR : ∀ z ∈ Metric.ball (0:E) r,
      HasFDerivAt R (f' (x+z)-f' x-B z) z := by
    intro z hz
    have hshift : HasFDerivAt (fun h : E => x+h) (ContinuousLinearMap.id ℝ E) z :=
      (hasFDerivAt_id z).const_add x
    have hbase := (hball hz).1.comp (f := fun h : E => x+h) z hshift
    have hquad : HasFDerivAt (fun v : E => B v v/2) (B z) z := by
      have H := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id z) (hasFDerivAt_id z)).const_smul (1/2:ℝ)
      have he : (fun v : E => B v v/2)=((1/2:ℝ) • fun v : E => B v v) := by
        ext v; simp only [Pi.smul_apply,smul_eq_mul] <;> ring
      rw [he]
      apply H.congr_fderiv
      ext v
      simp only [smul_apply,add_apply,ContinuousLinearMap.precompR_apply,
        ContinuousLinearMap.precompL_apply,ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,smul_eq_mul,id_eq]
      rw [hs v z]
      ring
    convert! ((hbase.sub_const (f x)).sub (f' x).hasFDerivAt).sub hquad using 1
    all_goals try with_reducible_and_instances rfl
  filter_upwards [Metric.ball_mem_nhds (0:E) hr] with h hh
  have hsub : Metric.closedBall (0:E) ‖h‖ ⊆ Metric.ball (0:E) r := by
    intro z hz
    simp only [Metric.mem_closedBall,Metric.mem_ball,dist_zero_right] at hz hh ⊢
    exact lt_of_le_of_lt hz hh
  have H := (convex_closedBall (0:E) ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hdR z (hsub hz)).hasFDerivWithinAt)
    (show ∀ z ∈ Metric.closedBall (0:E) ‖h‖, ‖f' (x+z)-f' x-B z‖≤ε*‖h‖ from by
      intro z hz
      exact (hball (hsub hz)).2.trans
        (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz) hε.le))
    (Metric.mem_closedBall_self (norm_nonneg h))
    (show h ∈ Metric.closedBall (0:E) ‖h‖ by simp)
  simpa only [hR0,sub_zero,R,add_zero,pow_two,Real.norm_eq_abs,abs_pow,
    abs_norm,abs_mul,mul_assoc] using H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_SmoothSupportSemibound
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_comp_with_acceleration {f : F → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f (g a))) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)+
        fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := g) x hgd
  have hd2 := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hd := hd1.clm_comp hd2
  have heq : (fun a => (fderiv ℝ f (g a)).comp (fderiv ℝ g a)) =ᶠ[𝓝 x]
      fderiv ℝ (fun a => f (g a)) := by
    filter_upwards [hgd.continuousAt.eventually (hf.eventually (by norm_num)),
      hg.eventually (by norm_num)] with a hfa hga
    exact ((hfa.differentiableAt (by norm_num)).hasFDerivAt.comp (f := g) a
      (hga.differentiableAt (by norm_num)).hasFDerivAt).fderiv.symm
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w)
    (hd.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [Function.comp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,add_apply,add_comm] using H

lemma HasSecondTaylor.smooth_support_diag_le {f q : E → ℝ}
    {l : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasSecondTaylor f l B) (hfd : HasFDerivAt f l 0)
    (hq : ContDiffAt ℝ 2 q 0) (hval : q 0=f 0)
    (hlo : q≤ᶠ[𝓝 0] f) (d:E) :
    fderiv ℝ (fderiv ℝ q) 0 d d≤B d d := by
  have hmin : IsLocalMin (fun x => f x-q x) 0 := by
    filter_upwards [hlo] with x hx
    change f 0-q 0≤f x-q x
    rw [hval,sub_self]
    linarith only [hx]
  have hlin := hmin.hasFDerivAt_eq_zero
    (hfd.sub (hq.differentiableAt (by norm_num)).hasFDerivAt)
  have Hj := hf.sub (hasSecondTaylor_of_contDiffAt hq)
  rw [hlin] at Hj
  let remainder := B - fderiv ℝ (fderiv ℝ q) 0
  have hnonneg : 0 ≤ remainder d d := by
    by_contra hnegative
    have hnegative : remainder d d < 0 := lt_of_not_ge hnegative
    have hdir : d ≠ 0 := by
      intro hzero
      subst d
      simp at hnegative
    have hnorm : 0 < ‖d‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hdir)
    let epsilon := -(remainder d d) / (4 * ‖d‖ ^ 2)
    have hepsilon : 0 < epsilon := div_pos (neg_pos.mpr hnegative) (by positivity)
    have hepsilon_mul : epsilon * ‖d‖ ^ 2 = -(remainder d d) / 4 := by
      dsimp [epsilon]
      field_simp
    obtain ⟨radius, hradius, hball⟩ :=
      Metric.eventually_nhds_iff.mp ((Hj.eventually hepsilon).and hmin)
    let delta := radius / (2 * (‖d‖ + 1))
    have hdelta : 0 < delta := div_pos hradius (by positivity)
    have hdelta_mul : delta * (2 * (‖d‖ + 1)) = radius :=
      div_mul_cancel₀ _ (by positivity)
    have hmem : delta • d ∈ Metric.ball (0 : E) radius := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hdelta]
      nlinarith [norm_nonneg d]
    obtain ⟨htaylor, hminimum⟩ := hball hmem
    change |f (delta • d) - q (delta • d) - (f 0 - q 0) - 0 -
      remainder (delta • d) (delta • d) / 2| ≤ epsilon * ‖delta • d‖ ^ 2 at htaylor
    have hbilinear : remainder (delta • d) (delta • d) = delta ^ 2 * remainder d d := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    have hscaled_norm : ‖delta • d‖ ^ 2 = delta ^ 2 * ‖d‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hdelta, mul_pow]
    rw [hbilinear, hscaled_norm] at htaylor
    have hupper := (abs_le.mp htaylor).2
    have hscaled_error : epsilon * (delta ^ 2 * ‖d‖ ^ 2) =
        delta ^ 2 * (-(remainder d d) / 4) := by
      calc
        _ = delta ^ 2 * (epsilon * ‖d‖ ^ 2) := by ring
        _ = _ := by rw [hepsilon_mul]
    rw [hscaled_error] at hupper
    have hstrict := mul_neg_of_pos_of_neg (sq_pos_of_pos hdelta) hnegative
    change f 0 - q 0 ≤ f (delta • d) - q (delta • d) at hminimum
    nlinarith
  change 0 ≤ B d d - fderiv ℝ (fderiv ℝ q) 0 d d at hnonneg
  linarith only [hnonneg]

lemma HasSecondTaylor.smooth_support_diag_le_at {f q : E → ℝ} {x : E}
    {l : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasSecondTaylor (fun h => f (x+h)) l B) (hfd : HasFDerivAt f l x)
    (hq : ContDiffAt ℝ 2 q x) (hval : q x=f x)
    (hlo : q≤ᶠ[𝓝 x] f) (d:E) :
    fderiv ℝ (fderiv ℝ q) x d d≤B d d := by
  have hc : ContinuousAt (fun h:E => x+h) 0 := continuousAt_const.add continuousAt_id
  have hq' : ContDiffAt ℝ 2 (fun h:E => q (x+h)) 0 := by
    exact (show ContDiffAt ℝ 2 q (x+0) by simpa only [add_zero] using hq).comp 0
      (contDiffAt_const.add contDiffAt_id)
  have hd : HasFDerivAt (fun h:E => f (x+h)) l 0 := by
    exact (hasFDerivAt_comp_add_left x).mpr (by simpa only [add_zero] using hfd)
  have hv : q (x+0)=f (x+0) := by simpa only [add_zero] using hval
  have hh : (fun h:E => q (x+h))≤ᶠ[𝓝 0] (fun h => f (x+h)) := by
    have ht : Tendsto (fun h:E => x+h) (𝓝 0) (𝓝 x) := by
      simpa only [add_zero] using hc.tendsto
    exact ht.eventually hlo
  have H := hf.smooth_support_diag_le hd hq' hv hh d
  have he : fderiv ℝ (fun h:E => q (x+h))=(fun h => fderiv ℝ q (x+h)) :=
    funext (fun h => fderiv_comp_add_left x)
  rw [he,fderiv_comp_add_left,add_zero] at H
  exact H

lemma bilinear_diag_sub_bound (B C : E →L[ℝ] E →L[ℝ] ℝ) (d:E) :
    |B d d-C d d|≤‖B-C‖*‖d‖^2 := by
  have H := (B-C).le_opNorm₂ d d
  simpa only [sub_apply,Real.norm_eq_abs,pow_two,mul_assoc] using H
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ShortEnvelopeSemibound
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_comp_at {f : F → ℝ} {g : E → F} {x : E}
    (hnear : ∀ᶠ y in 𝓝 (g x),DifferentiableAt ℝ f y)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (g x))
    (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f (g a))) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)+
        fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 := hf.hasFDerivAt.comp (f := g) x hgd
  have hd2 := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hd := hd1.clm_comp hd2
  have heq : (fun a => (fderiv ℝ f (g a)).comp (fderiv ℝ g a)) =ᶠ[𝓝 x]
      fderiv ℝ (fun a => f (g a)) := by
    filter_upwards [hgd.continuousAt.eventually hnear,hg.eventually (by norm_num)]
      with a hfa hga
    exact (hfa.hasFDerivAt.comp (f := g) a
      (hga.differentiableAt (by norm_num)).hasFDerivAt).fderiv.symm
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w)
    (hd.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [Function.comp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,add_apply,add_comm] using H

lemma second_fderiv_comp_minorant_le {f q : F → ℝ} {g : E → F} {x : E}
    (hnear : ∀ᶠ y in 𝓝 (g x),DifferentiableAt ℝ f y)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (g x))
    (hq : ContDiffAt ℝ 2 q (g x)) (hg : ContDiffAt ℝ 2 g x)
    (hval : q (g x)=f (g x)) (hlo : q≤ᶠ[𝓝 (g x)] f) (d:E) :
    fderiv ℝ (fderiv ℝ (fun a => q (g a))) x d d≤
      fderiv ℝ (fderiv ℝ (fun a => f (g a))) x d d := by
  have hd := (hnear.self_of_nhds).hasFDerivAt
  have hmin : IsLocalMin (fun y => f y-q y) (g x) := by
    filter_upwards [hlo] with y hy
    change f (g x)-q (g x)≤f y-q y
    rw [hval,sub_self]
    linarith only [hy]
  have hD : fderiv ℝ f (g x)=fderiv ℝ q (g x) :=
    sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero
      (hd.sub (hq.differentiableAt (by norm_num)).hasFDerivAt))
  have hj := hasSecondTaylor_of_second_derivative
    (hnear.mono (fun y hy => hy.hasFDerivAt)) hf.hasFDerivAt
  have H := hj.smooth_support_diag_le_at hd hq hval hlo (fderiv ℝ g x d)
  rw [second_fderiv_comp_with_acceleration hq hg,
    second_fderiv_comp_at hnear hf hg,hD]
  linarith only [H]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ShortEnvelopeJetTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma secondJetPullback_apply (j : F →L[ℝ] ℝ) (h : F →L[ℝ] F →L[ℝ] ℝ)
    (m : E →L[ℝ] F) (r : E →L[ℝ] E →L[ℝ] F) (v w : E) :
    secondJetPullback j h m r v w=h (m v) (m w)+j (r v w) := rfl

lemma secondJetPullback_tendsto {ι : Type*} {L : Filter ι}
    {j : ι → F →L[ℝ] ℝ} {h : ι → F →L[ℝ] F →L[ℝ] ℝ}
    {m : ι → E →L[ℝ] F} {r : ι → E →L[ℝ] E →L[ℝ] F}
    {j₀ : F →L[ℝ] ℝ} {h₀ : F →L[ℝ] F →L[ℝ] ℝ}
    {m₀ : E →L[ℝ] F} {r₀ : E →L[ℝ] E →L[ℝ] F}
    (hj : Tendsto j L (𝓝 j₀)) (hh : Tendsto h L (𝓝 h₀))
    (hm : Tendsto m L (𝓝 m₀)) (hr : Tendsto r L (𝓝 r₀)) :
    Tendsto (fun i => secondJetPullback (j i) (h i) (m i) (r i)) L
      (𝓝 (secondJetPullback j₀ h₀ m₀ r₀)) := by
  let : NormedAddCommGroup (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  have hm' := (((ContinuousLinearMap.compL ℝ E F ℝ).flip).continuous.tendsto m₀).comp hm
  have hh' := ((ContinuousLinearMap.compL ℝ E F (F →L[ℝ] ℝ)).continuous₂.tendsto (h₀,m₀)).comp
    (hh.prodMk_nhds hm)
  have hfirst := ((ContinuousLinearMap.compL ℝ E (F →L[ℝ] ℝ) (E →L[ℝ] ℝ)).continuous₂.tendsto
    (((ContinuousLinearMap.compL ℝ E F ℝ).flip) m₀,h₀.comp m₀)).comp (hm'.prodMk_nhds hh')
  have hj' := ((ContinuousLinearMap.compL ℝ E F ℝ).continuous.tendsto j₀).comp hj
  have hsecond := ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] F) (E →L[ℝ] ℝ)).continuous₂.tendsto
    (ContinuousLinearMap.compL ℝ E F ℝ j₀,r₀)).comp (hj'.prodMk_nhds hr)
  exact hfirst.add hsecond

lemma rough_smooth_pullback_limit_semibound {ι : Type*} {L : Filter ι}
    {f q : ι → F → ℝ} {g : ι → E → F} {x : ι → E}
    {j₀ : F →L[ℝ] ℝ} {h₀ : F →L[ℝ] F →L[ℝ] ℝ}
    {m₀ : E →L[ℝ] F} {r₀ : E →L[ℝ] E →L[ℝ] F}
    (hjet : ∀ᶠ i in L,
      (∀ᶠ y in 𝓝 (g i (x i)),DifferentiableAt ℝ (f i) y) ∧
      DifferentiableAt ℝ (fderiv ℝ (f i)) (g i (x i)) ∧
      ContDiffAt ℝ 2 (q i) (g i (x i)) ∧ ContDiffAt ℝ 2 (g i) (x i) ∧
      q i (g i (x i))=f i (g i (x i)) ∧ q i≤ᶠ[𝓝 (g i (x i))] f i)
    (hj : Tendsto (fun i => fderiv ℝ (q i) (g i (x i))) L (𝓝 j₀))
    (hh : Tendsto (fun i => fderiv ℝ (fderiv ℝ (q i)) (g i (x i))) L (𝓝 h₀))
    (hm : Tendsto (fun i => fderiv ℝ (g i) (x i)) L (𝓝 m₀))
    (hr : Tendsto (fun i => fderiv ℝ (fderiv ℝ (g i)) (x i)) L (𝓝 r₀))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ i in L,∀ d:E, secondJetPullback j₀ h₀ m₀ r₀ d d-ε*‖d‖^2≤
      fderiv ℝ (fderiv ℝ (fun a => f i (g i a))) (x i) d d := by
  have Hlim := secondJetPullback_tendsto hj hh hm hr
  have Hsmall := ((Metric.tendsto_nhds (α := E →L[ℝ] E →L[ℝ] ℝ)).mp Hlim) ε hε
  filter_upwards [hjet,Hsmall] with i hi hs
  intro d
  have Hle := second_fderiv_comp_minorant_le hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1
    hi.2.2.2.2.1 hi.2.2.2.2.2 d
  rw [second_fderiv_comp_with_acceleration hi.2.2.1 hi.2.2.2.1] at Hle
  have Habs := (abs_le.mp (bilinear_diag_sub_bound
    (secondJetPullback (fderiv ℝ (q i) (g i (x i)))
      (fderiv ℝ (fderiv ℝ (q i)) (g i (x i)))
      (fderiv ℝ (g i) (x i)) (fderiv ℝ (fderiv ℝ (g i)) (x i)))
    (secondJetPullback j₀ h₀ m₀ r₀) d)).1
  rw [dist_eq_norm
    (secondJetPullback (fderiv ℝ (q i) (g i (x i)))
      (fderiv ℝ (fderiv ℝ (q i)) (g i (x i)))
      (fderiv ℝ (g i) (x i)) (fderiv ℝ (fderiv ℝ (g i)) (x i)))
    (secondJetPullback j₀ h₀ m₀ r₀)] at hs
  have Hmul := mul_le_mul_of_nonneg_right hs.le (sq_nonneg ‖d‖)
  rw [secondJetPullback_apply] at Habs
  linarith only [Hle,Habs,Hmul]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ShortPullbackSemibound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section ShortPullbackSemibound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma parametric_short_pullback_semibound_oai {a : M} {ψ : P×Model n → ℝ}
    {p : P} {x : Model n} (L : ℝ≥0)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x))
    {pj : ℕ → P} {xj : ℕ → Model n} {tj : ℕ → ℝ} {f : ℕ → M → ℝ}
    (hp : Tendsto pj atTop (𝓝 p)) (hxx : Tendsto xj atTop (𝓝 x))
    (ht : Tendsto tj atTop (𝓝 0)) (htpos : ∀ᶠ i in atTop,0<tj i)
    (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
    (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) a).symm w))
    (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) a).symm (xj i))=ψ (pj i,xj i))
    {g : ℕ → E → Model n} {y : ℕ → E}
    (hgxy : ∀ᶠ i in atTop,g i (y i)=parametricShortForward a ψ ((pj i,tj i),xj i))
    (hjet : ∀ᶠ i in atTop,
      (∀ᶠ z in 𝓝 (g i (y i)),DifferentiableAt ℝ
        (fun z=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm z)) z) ∧
      DifferentiableAt ℝ (fderiv ℝ
        (fun z=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm z))) (g i (y i)) ∧
      ContDiffAt ℝ 2 (g i) (y i))
    {m : E →L[ℝ] Model n} {r : E →L[ℝ] E →L[ℝ] Model n}
    (hm : Tendsto (fun i=>fderiv ℝ (g i) (y i)) atTop (𝓝 m))
    (hr : Tendsto (fun i=>fderiv ℝ (fderiv ℝ (g i)) (y i)) atTop (𝓝 r))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ i in atTop,∀ d:E,
      secondJetPullback (fderiv ℝ (fun w=>ψ (p,w)) x)
        (fderiv ℝ (fderiv ℝ (fun w=>ψ (p,w))) x) m r d d-ε*‖d‖^2≤
        fderiv ℝ (fderiv ℝ (fun w=>hopfLax (tj i) (f i)
          ((extChartAt 𝓘(ℝ,Model n) a).symm (g i w)))) (y i) d d := by
  obtain ⟨U,hU,hD,hH⟩ := exists_parametric_short_lower_sequence L hx hψ hp hxx ht htpos hlip hbelow htouch
  have hj : ∀ᶠ i in atTop,
      (∀ᶠ z in 𝓝 (g i (y i)),DifferentiableAt ℝ
        (fun z=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm z)) z) ∧
      DifferentiableAt ℝ (fderiv ℝ
        (fun z=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm z))) (g i (y i)) ∧
      ContDiffAt ℝ 2 (U i) (g i (y i)) ∧ ContDiffAt ℝ 2 (g i) (y i) ∧
      U i (g i (y i))=hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm (g i (y i))) ∧
      U i≤ᶠ[𝓝 (g i (y i))] (fun z=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm z)) := by
    filter_upwards [hU,hjet,hgxy] with i hUi hji he
    rw [←he] at hUi
    exact ⟨hji.1,hji.2.1,hUi.1,hji.2.2,hUi.2.1,hUi.2.2⟩
  apply rough_smooth_pullback_limit_semibound hj ?_ ?_ hm hr hε
  · exact hD.congr' (hgxy.mono (fun i hi=>congrArg (fderiv ℝ (U i)) hi.symm))
  · exact hH.congr' (hgxy.mono (fun i hi=>congrArg (fderiv ℝ (fderiv ℝ (U i))) hi.symm))

end ShortPullbackSemibound
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.WeakMTWTransport.parametric_short_pullback_semibound_oai.{u_1, u_2, u_3} := @OAI.WeakMTWTransport.parametric_short_pullback_semibound_oai.{u_1, u_2, u_3}
