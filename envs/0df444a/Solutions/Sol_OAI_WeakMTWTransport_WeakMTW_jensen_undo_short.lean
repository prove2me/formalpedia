-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.jensen_undo_short
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:41:21.078239+00:00
-- url     : https://prove2.me/submissions/85f299de-da91-4209-bc94-af7c05929406

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

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ScalarExpansion
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
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma quadratic_expansion_polynomial_remainder {f:E → ℝ} {p:E} {A:E →L[ℝ] E}
    (hf:HasQuadraticExpansion f p A) :
    (fun h=>f h-quadraticTaylor (f 0) p A h)=o[𝓝 0] (fun h:E=>‖h‖^2) := by
  apply IsLittleO.of_bound
  intro ε hε
  obtain ⟨r,hr,H⟩:=hf ε hε
  filter_upwards [Metric.ball_mem_nhds (0:E) hr] with h hh
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖h‖)] using
    H h (by simpa only [Metric.mem_ball,dist_zero_right] using hh)

omit [CompleteSpace E] in
lemma HasSecondTaylor.of_littleO_difference {f g:E → ℝ}
    {l:E →L[ℝ] ℝ} {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hg:HasSecondTaylor g l B) (h0:f 0=g 0)
    (hfg:(fun h=>f h-g h)=o[𝓝 0] (fun h:E=>‖h‖^2)) : HasSecondTaylor f l B := by
  unfold HasSecondTaylor at hg ⊢
  convert! hfg.add hg using 1
  all_goals try with_reducible_and_instances rfl
  funext h
  rw [h0]
  ring

omit [CompleteSpace E] in
lemma quadratic_expansion_scalar_proxy {f:E → ℝ} {p:E} {A:E →L[ℝ] E}
    (hf:HasQuadraticExpansion f p A) {φ:ℝ → ℝ} (hφ:ContDiffAt ℝ 2 φ (f 0)) :
    let P:=quadraticTaylor (f 0) p A
    HasSecondTaylor (fun h=>φ (f h)) (fderiv ℝ (fun h=>φ (P h)) 0)
      (fderiv ℝ (fderiv ℝ (fun h=>φ (P h))) 0) := by
  let P:=quadraticTaylor (f 0) p A
  have hP:ContDiff ℝ 2 P := by
    dsimp only [P,quadraticTaylor]
    exact (contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).add
      ((A.contDiff.inner ℝ contDiff_id).div_const 2)
  have hp0:P 0=f 0 := by simp only [P,quadraticTaylor,map_zero,inner_zero_right,zero_div,add_zero]
  have hQ:ContDiffAt ℝ 2 (fun h=>φ (P h)) 0 := (hp0.symm ▸ hφ).comp 0 hP.contDiffAt
  apply (hasSecondTaylor_of_contDiffAt hQ).of_littleO_difference
  · simp only [hp0]
  · obtain ⟨K,s,hs,hK⟩:=(hφ.of_le (by norm_num : (1:WithTop ℕ∞)≤2)).exists_lipschitzOnWith
    have hpc:Tendsto P (𝓝 0) (𝓝 (f 0)) := hp0 ▸ hP.continuous.continuousAt.tendsto
    have hrem:Tendsto (fun vector => f vector-P vector) (𝓝 0) (𝓝 0) :=
      (quadratic_expansion_polynomial_remainder hf).trans_tendsto (by
        simpa using (continuous_norm.tendsto (0:E)).pow 2)
    have hfc:ContinuousAt f 0 := by
      change Tendsto f (𝓝 0) (𝓝 (f 0))
      simpa only [sub_add_cancel,zero_add] using hrem.add hpc
    have H:(fun h=>φ (f h)-φ (P h))=O[𝓝 0] (fun h=>f h-P h) := by
      apply IsBigO.of_bound (K:ℝ)
      filter_upwards [hfc hs,hpc hs] with h hf hs
      simpa only [dist_eq_norm] using hK.dist_le_mul (f h) hf (P h) hs
    exact H.trans_isLittleO (quadratic_expansion_polynomial_remainder hf)

lemma quadratic_expansion_scalar_exists [FiniteDimensional ℝ E] {f:E → ℝ} {p:E} {A:E →L[ℝ] E}
    (hf:HasQuadraticExpansion f p A) {φ:ℝ → ℝ} (hφ:ContDiffAt ℝ 2 φ (f 0)) :
    ∃q:E,∃B:E →L[ℝ] E,(∀d e,inner ℝ (B d) e=inner ℝ d (B e)) ∧
      HasQuadraticExpansion (fun h=>φ (f h)) q B := by
  let P:=quadraticTaylor (f 0) p A
  have hP:ContDiff ℝ 2 P := by
    dsimp only [P,quadraticTaylor]
    exact (contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).add
      ((A.contDiff.inner ℝ contDiff_id).div_const 2)
  have hp0:P 0=f 0 := by simp only [P,quadraticTaylor,map_zero,inner_zero_right,zero_div,add_zero]
  have hQ:ContDiffAt ℝ 2 (fun h=>φ (P h)) 0 := (hp0.symm ▸ hφ).comp 0 hP.contDiffAt
  have H:=quadratic_expansion_scalar_proxy hf hφ
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun h=>φ (P h)) 0),
    bilinearOperator (fderiv ℝ (fderiv ℝ (fun h=>φ (P h))) 0),?_,?_⟩
  · intro first second
    rw [bilinearOperator_inner]
    calc
      _ = fderiv ℝ (fderiv ℝ (fun h=>φ (P h))) 0 second first :=
        (hQ.isSymmSndFDerivAt (by norm_num)).eq first second
      _ = _ := by rw [real_inner_comm,bilinearOperator_inner]
  · intro epsilon hepsilon
    obtain ⟨radius,hradius,hball⟩ := Metric.eventually_nhds_iff.mp (H.eventually hepsilon)
    refine ⟨radius,hradius,?_⟩
    intro vector hvector
    have hbound := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hvector)
    simpa only [P,quadraticTaylor,bilinearOperator_inner,InnerProductSpace.toDual_symm_apply,
      sub_add_eq_sub_sub] using hbound
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_SubgradientDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma quadraticTaylor_increment (f0 : ℝ) (p : E) (A : E →L[ℝ] E)
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)) (h e : E) (t : ℝ) :
    quadraticTaylor f0 p A (h + t • e) - quadraticTaylor f0 p A h =
      t * inner ℝ (p + A h) e + t ^ 2 / 2 * inner ℝ (A e) e := by
  have hs : inner ℝ (A e) h = inner ℝ (A h) e := (hA e h).trans (real_inner_comm _ _)
  simp only [quadraticTaylor, map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hs]
  ring

lemma subgradient_directional_bound {f : E → ℝ} {f0 : ℝ} {p h zeta e : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    {r alpha w : ℝ} (hr : 0 < r) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hw : 0 ≤ w) (hh : ‖h‖ ≤ r) (he : ‖e‖ = 1)
    (hrem : ∀ z : E, ‖z‖ ≤ 2*r →
      |f z - quadraticTaylor f0 p A z| ≤ w * ‖z‖ ^ 2)
    (hsub : IsSubgradientOn f (Metric.closedBall 0 (2*r)) h zeta) :
    inner ℝ (zeta - p - A h) e ≤ ‖A‖ * alpha * r / 2 + 5*w*r/alpha := by
  have hat : 0 < alpha*r := mul_pos ha hr
  have hz : ‖h + (alpha*r) • e‖ ≤ 2*r := by
    calc
      ‖h + (alpha*r) • e‖ ≤ ‖h‖ + ‖(alpha*r) • e‖ := norm_add_le _ _
      _ = ‖h‖ + alpha*r := by rw [norm_smul_of_nonneg hat.le, he, mul_one]
      _ ≤ 2*r := by nlinarith
  have hxbound := hrem h (by linarith)
  have hzbound := hrem (h + (alpha*r) • e) hz
  have hsg := hsub (h + (alpha*r) • e) (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  have hnormsq : ‖h + (alpha*r) • e‖ ^ 2 ≤ 4*r^2 := by
    nlinarith [norm_nonneg (h + (alpha*r) • e)]
  have hhsq : ‖h‖ ^ 2 ≤ r^2 := by nlinarith [norm_nonneg h]
  have hremdiff : (f (h + (alpha*r) • e) - quadraticTaylor f0 p A (h + (alpha*r) • e)) -
      (f h - quadraticTaylor f0 p A h) ≤ 5*w*r^2 := by
    have h1 := (abs_le.mp hzbound).2
    have h2 := (abs_le.mp hxbound).1
    have h3 := mul_le_mul_of_nonneg_left hnormsq hw
    have h4 := mul_le_mul_of_nonneg_left hhsq hw
    nlinarith
  have hquad := quadraticTaylor_increment f0 p A hA h e (alpha*r)
  have hAe : inner ℝ (A e) e ≤ ‖A‖ := by
    calc
      inner ℝ (A e) e ≤ ‖inner ℝ (A e) e‖ := le_abs_self _
      _ ≤ ‖A e‖ * ‖e‖ := norm_inner_le_norm _ _
      _ ≤ ‖A‖ := by simpa only [he, mul_one] using A.le_opNorm e
  simp only [add_sub_cancel_left, real_inner_smul_right] at hsg
  have hdir : alpha*r * inner ℝ (zeta - p - A h) e ≤
      (alpha*r)^2/2 * ‖A‖ + 5*w*r^2 := by
    simp only [inner_sub_left, inner_add_left] at hquad ⊢
    have hm := mul_le_mul_of_nonneg_left hAe (by positivity : 0 ≤ (alpha*r)^2/2)
    nlinarith
  apply (mul_le_mul_iff_right₀ hat).mp
  have hcancel : (5*w*r/alpha) * (alpha*r) = 5*w*r^2 := by field_simp
  nlinarith

lemma subgradient_norm_bound {f : E → ℝ} {f0 : ℝ} {p h zeta : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    {r alpha w : ℝ} (hr : 0 < r) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hw : 0 ≤ w) (hh : ‖h‖ ≤ r)
    (hrem : ∀ z : E, ‖z‖ ≤ 2*r →
      |f z - quadraticTaylor f0 p A z| ≤ w * ‖z‖ ^ 2)
    (hsub : IsSubgradientOn f (Metric.closedBall 0 (2*r)) h zeta) :
    ‖zeta - p - A h‖ ≤ ‖A‖ * alpha * r / 2 + 5*w*r/alpha := by
  by_cases hzero : zeta - p - A h = 0
  · rw [hzero, norm_zero]
    positivity
  let v := zeta - p - A h
  let e := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hzero
  have hd := subgradient_directional_bound hA hr ha ha1 hw hh he hrem hsub
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hzero
  have hip : inner ℝ (zeta - p - A h) e = ‖zeta - p - A h‖ := by
    change inner ℝ v (‖v‖⁻¹ • v) = ‖v‖
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  exact hip ▸ hd

lemma subgradient_zero_of_quadraticExpansion {f : E → ℝ} {p zeta : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0 < R)
    (hsub : IsSubgradientOn f (Metric.ball 0 R) 0 zeta) : zeta = p := by
  obtain ⟨delta, hdelta, hrem⟩ := hexp 1 zero_lt_one
  let eps := min R delta / 4
  have heps : 0 < eps := by dsimp [eps] <;> positivity
  have hbound (r : ℝ) (hr : r ∈ Ioo 0 eps) :
      ‖zeta - p‖ ≤ ‖A‖ * 1 * r / 2 + 5*1*r/1 := by
    have hrR : 2*r < R := by
      have hh : 4*eps ≤ R := by dsimp [eps] <;> linarith [min_le_left R delta]
      linarith [hr.2]
    have hrdelta : 2*r < delta := by
      have hh : 4*eps ≤ delta := by dsimp [eps] <;> linarith [min_le_right R delta]
      linarith [hr.2]
    have hh := subgradient_norm_bound (p := p) (h := 0) hA hr.1 zero_lt_one
      le_rfl zero_le_one (by simpa using hr.1.le)
      (fun z hz => hrem z (hz.trans_lt hrdelta))
      (fun z hz => hsub z (by
        rw [Metric.mem_ball, dist_zero_right]
        exact (show ‖z‖ ≤ 2 * r from by simpa only [Metric.mem_closedBall, dist_zero_right] using hz).trans_lt hrR))
    simpa only [map_zero, sub_zero] using hh
  have hcl : (0 : ℝ) ∈ closure (Ioo 0 eps) := by
    rw [closure_Ioo heps.ne]
    exact ⟨le_rfl, heps.le⟩
  have hcont : Continuous (fun r : ℝ => ‖A‖ * 1 * r / 2 + 5*1*r/1) := by fun_prop
  have hlim := ContinuousWithinAt.closure_le hcl
    (continuousWithinAt_const (b := ‖zeta-p‖)) hcont.continuousWithinAt hbound
  have hz : ‖zeta-p‖ = 0 := le_antisymm (by simpa using hlim) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma subgradient_uniform_differential {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0 < R) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ h zeta : E, ‖h‖ < delta → IsSubgradientOn f (Metric.ball 0 R) h zeta →
        ‖zeta - p - A h‖ ≤ eps * ‖h‖ := by
  intro eps heps
  let alpha : ℝ := min 1 (eps / (‖A‖ + 1))
  have ha : 0 < alpha := by dsimp [alpha] <;> positivity
  have ha1 : alpha ≤ 1 := min_le_left _ _
  have hAa : ‖A‖ * alpha ≤ eps := by
    have hh := (le_div_iff₀ (by positivity : 0 < ‖A‖ + 1)).mp (min_le_right 1 (eps/(‖A‖+1)))
    change alpha * (‖A‖+1) ≤ eps at hh
    nlinarith
  let w : ℝ := eps * alpha / 20
  have hw : 0 < w := by dsimp [w] <;> positivity
  obtain ⟨d, hd, hrem⟩ := hexp w hw
  let delta := min R d / 4
  have hdelta : 0 < delta := by dsimp [delta] <;> positivity
  refine ⟨delta, hdelta, ?_⟩
  intro h zeta hh hsub
  by_cases hz : h = 0
  · subst h
    have hzet := subgradient_zero_of_quadraticExpansion hA hexp hR hsub
    simp [hzet]
  have hnorm : 0 < ‖h‖ := norm_pos_iff.mpr hz
  have hhr : 2*‖h‖ < R := by
    have ht : 4*delta ≤ R := by dsimp [delta] <;> linarith [min_le_left R d]
    linarith
  have hhd : 2*‖h‖ < d := by
    have ht : 4*delta ≤ d := by dsimp [delta] <;> linarith [min_le_right R d]
    linarith
  have hb := subgradient_norm_bound hA hnorm ha ha1 hw.le le_rfl
    (fun z hz => hrem z (hz.trans_lt hhd))
    (fun z hz => hsub z (by
      rw [Metric.mem_ball, dist_zero_right]
      exact (show ‖z‖ ≤ 2 * ‖h‖ from by simpa only [Metric.mem_closedBall, dist_zero_right] using hz).trans_lt hhr))
  apply hb.trans
  have hwcalc : 5*w*‖h‖/alpha = eps*‖h‖/4 := by
    dsimp [w]
    field_simp
    ring
  rw [hwcalc]
  have hm := mul_le_mul_of_nonneg_right hAa hnorm.le
  nlinarith

lemma semiconvex_subgradient_iff {f : E → ℝ} {s : Set E} {K : ℝ} {h zeta : E} :
    IsSemiconvexSubgradientOn f s K h zeta ↔
      IsSubgradientOn (fun x => f x + K / 2 * ‖x‖ ^ 2) s h (zeta + K • h) := by
  have heq (y : E) :
      f h + K / 2 * ‖h‖ ^ 2 + inner ℝ (zeta + K • h) (y - h) -
          (f y + K / 2 * ‖y‖ ^ 2) =
      f h + inner ℝ zeta (y-h) - K/2*‖y-h‖^2 - f y := by
    simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_sub_left,
      inner_sub_right, real_inner_smul_left]
    rw [real_inner_comm y h]
    ring
  constructor <;> intro hs y hy
  · have hh := hs y hy
    linarith [heq y]
  · have hh := hs y hy
    linarith [heq y]

lemma quadraticExpansion_add_quadratic {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hexp : HasQuadraticExpansion f p A) (K : ℝ) :
    HasQuadraticExpansion (fun x => f x + K / 2 * ‖x‖ ^ 2) p
      (A + K • ContinuousLinearMap.id ℝ E) := by
  intro w hw
  obtain ⟨d, hd, hr⟩ := hexp w hw
  refine ⟨d, hd, fun z hz => ?_⟩
  have heq : (f z + K/2*‖z‖ ^ 2) -
      quadraticTaylor (f 0 + K/2*‖(0 : E)‖ ^ 2) p
        (A + K • ContinuousLinearMap.id ℝ E) z = f z - quadraticTaylor (f 0) p A z := by
    simp only [quadraticTaylor, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero,
      add_zero, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [heq]
  exact hr z hz

lemma semiconvex_subgradient_uniform_differential {f : E → ℝ} {p : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0 < R) (K : ℝ) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ h zeta : E, ‖h‖ < delta →
        IsSemiconvexSubgradientOn f (Metric.ball 0 R) K h zeta →
        ‖zeta - p - A h‖ ≤ eps * ‖h‖ := by
  have hs : ∀ x y : E,
      inner ℝ ((A + K • ContinuousLinearMap.id ℝ E) x) y =
        inner ℝ x ((A + K • ContinuousLinearMap.id ℝ E) y) := by
    intro x y
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hA]
  intro eps heps
  obtain ⟨delta, hdelta, hb⟩ := subgradient_uniform_differential hs
    (quadraticExpansion_add_quadratic hexp K) hR eps heps
  refine ⟨delta, hdelta, ?_⟩
  intro h zeta hh hsub
  have hhbound := hb h (zeta + K • h) hh (semiconvex_subgradient_iff.mp hsub)
  have heq : zeta + K • h - p - (A + K • ContinuousLinearMap.id ℝ E) h =
      zeta - p - A h := by
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply]
    abel
  rwa [heq] at hhbound


end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ProximalSelectorDerivative
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma semiconvex_subgradient_along_selector {f : E → ℝ} {Y ξ : E → E}
    {x p : E} {A R : E →L[ℝ] E}
    (hA : ∀ v w, inner ℝ (A v) w=inner ℝ v (A w))
    (hexp : HasQuadraticExpansion (fun h => f (Y x+h)) p A)
    {r : ℝ} (hr : 0 < r) (K : ℝ) (hY : HasFDerivAt Y R x)
    (hξ : ξ x=p)
    (hg : ∀ᶠ z in 𝓝 x,
      IsSemiconvexSubgradientOn f (Metric.ball (Y x) r) K (Y z) (ξ z)) :
    HasFDerivAt ξ (A.comp R) x := by
  obtain ⟨C,hC,hCb⟩ := hY.isBigO_sub.exists_pos
  have hs : (fun z => ξ z-p-A (Y z-Y x)) =o[𝓝 x] (fun z => z-x) := by
    rw [Asymptotics.isLittleO_iff]
    intro eps heps
    obtain ⟨d,hd,H⟩ := semiconvex_subgradient_uniform_differential hA hexp hr K
      (eps/C) (div_pos heps hC)
    have hn : ∀ᶠ z in 𝓝 x, ‖Y z-Y x‖ < d := by
      simpa only [Metric.mem_ball,dist_eq_norm] using
        hY.continuousAt.eventually (Metric.ball_mem_nhds (Y x) hd)
    filter_upwards [hg,hCb.bound,hn] with z hz hbound hnear
    have HH := H (Y z-Y x) (ξ z) hnear (by
      intro w hw
      have hw' : Y x+w∈Metric.ball (Y x) r := by
        simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hw
      have hh := hz (Y x+w) hw'
      simpa only [add_sub_cancel,show w-(Y z-Y x)=Y x+w-Y z by abel] using hh)
    calc
      ‖ξ z-p-A (Y z-Y x)‖ ≤ (eps/C)*‖Y z-Y x‖ := HH
      _ ≤ (eps/C)*(C*‖z-x‖) := mul_le_mul_of_nonneg_left hbound (div_nonneg heps.le hC.le)
      _ = eps*‖z-x‖ := by field_simp
  have ha := A.hasFDerivAt.comp x hY
  rw [hasFDerivAt_iff_isLittleO] at ha ⊢
  convert hs.add ha using 1
  all_goals try with_reducible_and_instances rfl
  first
  | rfl
  | (ext z
     simp only [Function.comp_def,ContinuousLinearMap.comp_apply,map_sub,hξ]
     abel)
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ProximalProducer
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma lower_contact_subgradient_on {f g : E → ℝ} {s : Set E}
    (hc : ConvexOn ℝ s f) {x : E} (hx : x∈s)
    {g' : E →L[ℝ] ℝ} (hg : HasFDerivAt g g' x)
    (heq : g x=f x) (hle : g≤ᶠ[𝓝 x]f) :
    IsSubgradientOn f s x ((InnerProductSpace.toDual ℝ E).symm g') := by
  intro v hv
  rw [InnerProductSpace.toDual_symm_apply]
  have hp : HasDerivAt (fun t : ℝ => x+t • (v-x)) (v-x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (v-x)).const_add x
  have hd : HasDerivAt (fun t : ℝ => g (x+t • (v-x))) (g' (v-x)) 0 := by
    exact (show HasFDerivAt g g' (x+(0:ℝ) • (v-x)) from by simpa using hg).comp_hasDerivAt 0 hp
  have htend : Tendsto (fun t : ℝ => x+t • (v-x)) (𝓝[>]0) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hb : ∀ᶠ t : ℝ in 𝓝[>]0,
      t⁻¹*(g (x+t • (v-x))-g x)≤f v-f x := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1),htend.eventually hle] with t ht htf
    have hcv := hc.2 hx hv (by linarith [ht.2] : 0≤1-t) ht.1.le (by ring : 1-t+t=1)
    have he : (1-t) • x+t • v=x+t • (v-x) := by
      simp only [sub_smul,one_smul,smul_sub]; abel
    rw [he] at hcv
    simp only [smul_eq_mul] at hcv
    rw [inv_mul_eq_div,div_le_iff₀ ht.1,heq]
    nlinarith only [hcv,htf]
  have hlim : Tendsto (fun t : ℝ => t⁻¹*(g (x+t • (v-x))-g x))
      (𝓝[>]0) (𝓝 (g' (v-x))) := by
    simpa only [zero_add,zero_smul,add_zero,smul_eq_mul] using hd.tendsto_slope_zero_right
  have H := le_of_tendsto hlim hb
  linarith only [H]

lemma lower_contact_semiconvex_subgradient_on {f g : E → ℝ} {s : Set E} {K : ℝ}
    (hc : ConvexOn ℝ s (fun z => f z+K/2*‖z‖^2)) {x : E} (hx : x∈s)
    {g' : E →L[ℝ] ℝ} (hg : HasFDerivAt g g' x)
    (heq : g x=f x) (hle : g≤ᶠ[𝓝 x]f) :
    IsSemiconvexSubgradientOn f s K x ((InnerProductSpace.toDual ℝ E).symm g') := by
  rw [semiconvex_subgradient_iff]
  have hq := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (K/2)
  have hh : (fun z => g z+K/2*‖z‖^2)≤ᶠ[𝓝 x](fun z => f z+K/2*‖z‖^2) := by
    filter_upwards [hle] with z hz
    linarith only [hz]
  have h := lower_contact_subgradient_on hc hx (hg.add hq) (by simp only [Pi.add_apply,heq]) hh
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [map_add,map_smul,LinearIsometryEquiv.apply_symm_apply]
  ext z
  simp only [add_apply,smul_apply,
    InnerProductSpace.toDual_apply_apply,innerSL_apply_apply,smul_eq_mul]
  ring

lemma kernel_minimum_semiconvex_subgradient {f k : E → ℝ} {s : Set E} {K : ℝ}
    (hc : ConvexOn ℝ s (fun z => f z+K/2*‖z‖^2)) {x : E} (hx : x∈s)
    {k' : E →L[ℝ] ℝ} (hk : HasFDerivAt k k' x)
    (hmin : ∀ᶠ y in 𝓝 x, f x+k x≤f y+k y) :
    IsSemiconvexSubgradientOn f s K x ((InnerProductSpace.toDual ℝ E).symm (-k')) := by
  apply lower_contact_semiconvex_subgradient_on hc hx
    (hk.neg.const_add (f x+k x)) (by simp only [Pi.neg_apply] <;> ring)
  filter_upwards [hmin] with y hy
  simp only [Pi.neg_apply]
  linarith only [hy]

omit [CompleteSpace E] in
lemma semiconvex_subgradient_eq_at_expansion {f : E → ℝ} {x p ξ : E}
    {A : E →L[ℝ] E} (hA : ∀ v w,inner ℝ (A v) w=inner ℝ v (A w))
    (hexp : HasQuadraticExpansion (fun h => f (x+h)) p A)
    {r : ℝ} (hr : 0 < r) (K : ℝ)
    (hsub : IsSemiconvexSubgradientOn f (Metric.ball x r) K x ξ) : ξ=p := by
  obtain ⟨d,hd,H⟩ := semiconvex_subgradient_uniform_differential hA hexp hr K 1 zero_lt_one
  have hh := H 0 ξ (by simpa using hd) (by
    intro w hw
    have hw' : x+w∈Metric.ball x r := by
      simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hw
    simpa only [add_zero,sub_zero,add_sub_cancel_left] using hsub (x+w) hw')
  have hn : ‖ξ-p‖≤0 := by simpa only [map_zero,sub_zero,norm_zero,mul_zero] using hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_PhaseGraphDerivative
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
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma semiconvex_phase_graph_derivative
    {f:E → ℝ} {Y:E → E} {P:E → E →L[ℝ] ℝ}
    {Φ:(E×(E →L[ℝ] ℝ)) → E×(E →L[ℝ] ℝ)}
    {x p:E} {A R:E →L[ℝ] E} {H:E →L[ℝ] E →L[ℝ] ℝ}
    {D:(E×(E →L[ℝ] ℝ)) →L[ℝ] E×(E →L[ℝ] ℝ)}
    (hA:∀v w,inner ℝ (A v) w=inner ℝ v (A w))
    (hexp:HasQuadraticExpansion (fun h=>f (Y x+h)) p A)
    {r:ℝ} (hr:0 < r) (K:ℝ)
    (hY:HasFDerivAt Y R x) (hP:HasFDerivAt P H x)
    (hΦ:HasFDerivAt Φ D (x,P x))
    (hbase:∀ᶠ z in 𝓝 x,(Φ (z,P z)).1=Y z)
    (hsub:∀ᶠ z in 𝓝 x,
      IsSemiconvexSubgradientOn f (Metric.ball (Y x) r) K (Y z)
        ((InnerProductSpace.toDual ℝ E).symm (Φ (z,P z)).2)) :
    D.comp ((ContinuousLinearMap.id ℝ E).prod H)=
      R.prod (((innerSL ℝ).comp A).comp R) := by
  let ξ:=fun z=>(InnerProductSpace.toDual ℝ E).symm (Φ (z,P z)).2
  have hξ:ξ x=p:=semiconvex_subgradient_eq_at_expansion hA hexp hr K hsub.self_of_nhds
  have hd:=semiconvex_subgradient_along_selector hA hexp hr K hY hξ hsub
  have hs:HasFDerivAt (fun z=>(Φ (z,P z)).2) (((innerSL ℝ).comp A).comp R) x := by
    have hh:HasFDerivAt (fun z=>(innerSL ℝ) (ξ z)) ((innerSL ℝ).comp (A.comp R)) x :=
      (innerSL ℝ).hasFDerivAt.comp x hd
    have he:(fun z=>(Φ (z,P z)).2)=(fun z=>(innerSL ℝ) (ξ z)) := by
      funext z
      exact ((InnerProductSpace.toDual ℝ E).apply_symm_apply (Φ (z,P z)).2).symm
    rw [he]
    simpa only [ContinuousLinearMap.comp_assoc] using hh
  have hb:HasFDerivAt (fun z=>(Φ (z,P z)).1) R x := hY.congr_of_eventuallyEq hbase
  have hboth:=hb.prodMk hs
  have hchain:=hΦ.comp x ((hasFDerivAt_id x).prodMk hP)
  exact hchain.unique hboth

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartGradientMap
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

omit [CompactSpace M] [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinateRaise_contDiffAt {a : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (fun q : Model n×(Model n →L[ℝ] ℝ) =>
      (q.1,(riemannianCoordinateMetric a q.1).inverse q.2)) q := by
  have hg := (contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hq)
  have hi := (riemannianCoordinateMetric_isInvertible hq).contDiffAt_map_inverse.comp q.1 hg
  exact contDiffAt_fst.prodMk ((hi.comp q contDiffAt_fst).clm_apply contDiffAt_snd)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_CotangentFlow
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

omit [CompactSpace M] [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma phaseLower_contDiffAt {a:M} {q:Model n × Model n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (phaseLower a) q := by
  have hg := (contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hq)
  exact contDiffAt_fst.prodMk ((hg.comp q contDiffAt_fst).clm_apply contDiffAt_snd)

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma phaseLower_raise {a:M} {q:Phase n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) : phaseLower a (phaseRaise a q)=q := by
  exact Prod.ext rfl ((riemannianCoordinateMetric_isInvertible hq).self_apply_inverse q.2)

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinatePhaseFlow_zero {a:M} {q:Phase n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) : coordinatePhaseFlow a (0,q)=q := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have ht:phaseRaise a q∈χ.target := (tangent_chart_target_iff _ _).mpr hq
  dsimp only [coordinatePhaseFlow]
  rw [neg_zero,sprayFlow_zero,χ.right_inv ht]
  exact phaseLower_raise hq

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinatePhaseFlow_contDiffAt {a:M} {q:Phase n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (coordinatePhaseFlow a) (0,q) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have ht:phaseRaise a q∈χ.target := (tangent_chart_target_iff _ _).mpr hq
  have hi := (contMDiffOn_extChartAt_symm (n := ∞) (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)).contMDiffAt
    ((isOpen_extChartAt_target _).mem_nhds ht)
  have hr:ContDiffAt ℝ ∞ (phaseRaise a) q := coordinateRaise_contDiffAt hq
  have hinput := hi.comp (f:=fun p:ℝ×Phase n=>phaseRaise a p.2) (0,q)
    (hr.comp (0,q) contDiffAt_snd).contMDiffAt
  have hf := contMDiff_sprayFlow.contMDiffAt.comp (f:=fun p:ℝ×Phase n=>
    (-p.1,χ.symm (phaseRaise a p.2))) (0,q)
    (contDiffAt_fst.neg.contMDiffAt.prodMk hinput)
  have he:sprayFlow (-(0:ℝ)) (χ.symm (phaseRaise a q))=χ.symm (phaseRaise a q) := by
    rw [neg_zero,sprayFlow_zero]
  have hc:ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      𝓘(ℝ,Model n × Model n) ∞ χ (sprayFlow (-(0:ℝ)) (χ.symm (phaseRaise a q))) := by
    rw [he]
    exact contMDiffAt_extChartAt' (by simpa only [χ,extChartAt_source] using χ.map_target ht)
  have hout := (hc.comp (f:=fun p:ℝ×Phase n=>
    sprayFlow (-p.1) (χ.symm (phaseRaise a p.2))) (0,q) hf).contDiffAt
  have hbase:(χ (sprayFlow (-(0:ℝ)) (χ.symm (phaseRaise a q)))).1∈
      (extChartAt 𝓘(ℝ,Model n) a).target := by
    rw [he,χ.right_inv ht]; exact hq
  exact (phaseLower_contDiffAt hbase).comp (0,q) hout

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinatePhaseFlow_derivative_limit {a:M} {q:Phase n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    Tendsto (fun p:ℝ×Phase n=>fderiv ℝ (fun v=>coordinatePhaseFlow a (p.1,v)) p.2)
      (𝓝 (0,q)) (𝓝 (ContinuousLinearMap.id ℝ (Phase n))) := by
  have hd := ContDiffAt.partial_snd_fderiv (f:=fun t v=>coordinatePhaseFlow a (t,v)) (coordinatePhaseFlow_contDiffAt hq)
  have he:(fun v:Phase n=>coordinatePhaseFlow a (0,v))=ᶠ[𝓝 q] id := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target a).mem_nhds hq)] with v hv
    exact coordinatePhaseFlow_zero hv
  have hev:fderiv ℝ (fun v=>coordinatePhaseFlow a (0,v)) q=ContinuousLinearMap.id ℝ (Phase n) := by
    rw [he.fderiv_eq,fderiv_id]
  simpa only [hev] using hd.continuousAt.tendsto

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_PhaseJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section PhaseJetAlgebra
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {P:Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma limit_from_comp_near_id {Aj Hj:ℕ → E →L[ℝ] P} {Rj:ℕ → E →L[ℝ] E}
    {H:E →L[ℝ] P} (hR:Tendsto Rj atTop (𝓝 1))
    (hH:Tendsto Hj atTop (𝓝 H))
    (he:∀ᶠ j in atTop,(Aj j).comp (Rj j)=Hj j) : Tendsto Aj atTop (𝓝 H) := by
  have hi:Tendsto (fun j=>Ring.inverse (Rj j)) atTop (𝓝 (1:E →L[ℝ] E)) := by
    simpa only [Function.comp_def, Units.val_one, Ring.inverse_one] using (NormedRing.inverse_continuousAt (1:(E →L[ℝ] E)ˣ)).tendsto.comp hR
  have hu:∀ᶠ j in atTop,IsUnit (Rj j) := hR.eventually (Units.isOpen.mem_nhds isUnit_one)
  have hl:= (ContinuousLinearMap.compL ℝ E E P).continuous₂.tendsto (H,1) |>.comp (hH.prodMk_nhds hi)
  change Tendsto (fun j=>(Hj j).comp (Ring.inverse (Rj j))) atTop (𝓝 H) at hl
  apply hl.congr'
  filter_upwards [he,hu] with j hej huj
  ext v
  have hh:=congrArg (fun T:E →L[ℝ] P=>T (Ring.inverse (Rj j) v)) hej
  have hr:Rj j (Ring.inverse (Rj j) v)=v :=
    congrArg (fun T:E →L[ℝ] E=>T v) (Ring.mul_inverse_cancel (Rj j) huj)
  simpa only [ContinuousLinearMap.comp_apply,hr] using hh.symm

lemma phase_graph_derivative_limit
    {Dj:ℕ → (E×P) →L[ℝ] (E×P)} {Hj Aj:ℕ → E →L[ℝ] P}
    {Rj:ℕ → E →L[ℝ] E} {H:E →L[ℝ] P}
    (hD:Tendsto Dj atTop (𝓝 (ContinuousLinearMap.id ℝ (E×P))))
    (hH:Tendsto Hj atTop (𝓝 H))
    (he:∀ᶠ j in atTop,(Dj j).comp ((ContinuousLinearMap.id ℝ E).prod (Hj j))=
      (Rj j).prod ((Aj j).comp (Rj j))) :
    Tendsto Rj atTop (𝓝 1) ∧ Tendsto Aj atTop (𝓝 H) := by
  have hpair:Tendsto (fun j=>(ContinuousLinearMap.id ℝ E).prod (Hj j)) atTop
      (𝓝 ((ContinuousLinearMap.id ℝ E).prod H)) := (ContinuousLinearMap.prodₗᵢ ℝ).continuous.tendsto _ |>.comp (tendsto_const_nhds.prodMk_nhds hH)
  have hd:= (ContinuousLinearMap.compL ℝ E (E×P) (E×P)).continuous₂.tendsto _ |>.comp (hD.prodMk_nhds hpair)
  change Tendsto (fun j=>(Dj j).comp ((ContinuousLinearMap.id ℝ E).prod (Hj j))) atTop
    (𝓝 ((ContinuousLinearMap.id ℝ (E×P)).comp ((ContinuousLinearMap.id ℝ E).prod H))) at hd
  rw [ContinuousLinearMap.id_comp] at hd
  have hd':Tendsto (fun j=>(Rj j).prod ((Aj j).comp (Rj j))) atTop
      (𝓝 ((ContinuousLinearMap.id ℝ E).prod H)) := hd.congr' he
  have hR:= (ContinuousLinearMap.compL ℝ E (E×P) E (ContinuousLinearMap.fst ℝ E P)).continuous.tendsto _ |>.comp hd'
  have hA:= (ContinuousLinearMap.compL ℝ E (E×P) P (ContinuousLinearMap.snd ℝ E P)).continuous.tendsto _ |>.comp hd'
  change Tendsto (fun j=>(ContinuousLinearMap.fst ℝ E P).comp ((Rj j).prod ((Aj j).comp (Rj j)))) atTop
    (𝓝 ((ContinuousLinearMap.fst ℝ E P).comp ((ContinuousLinearMap.id ℝ E).prod H))) at hR
  simp only [ContinuousLinearMap.fst_comp_prod] at hR
  change Tendsto (fun j=>(ContinuousLinearMap.snd ℝ E P).comp ((Rj j).prod ((Aj j).comp (Rj j)))) atTop
    (𝓝 ((ContinuousLinearMap.snd ℝ E P).comp ((ContinuousLinearMap.id ℝ E).prod H))) at hA
  simp only [ContinuousLinearMap.snd_comp_prod] at hA
  exact ⟨hR,limit_from_comp_near_id hR hA (Eventually.of_forall (fun _=>rfl))⟩
end PhaseJetAlgebra

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinate_phase_jet_limit {a:M} {q:Phase n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    {τj:ℕ → ℝ} {qj:ℕ → Phase n} {Hj Aj:ℕ → Model n →L[ℝ] Model n →L[ℝ] ℝ}
    {Rj:ℕ → Model n →L[ℝ] Model n} {H:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (ht:Tendsto τj atTop (𝓝 0)) (hqj:Tendsto qj atTop (𝓝 q))
    (hH:Tendsto Hj atTop (𝓝 H))
    (he:∀ᶠ j in atTop,
      (fderiv ℝ (fun v=>coordinatePhaseFlow a (τj j,v)) (qj j)).comp
        ((ContinuousLinearMap.id ℝ (Model n)).prod (Hj j))=
      (Rj j).prod ((Aj j).comp (Rj j))) :
    Tendsto Rj atTop (𝓝 1) ∧ Tendsto Aj atTop (𝓝 H) := by
  have hd := (coordinatePhaseFlow_derivative_limit hq).comp (ht.prodMk_nhds hqj)
  exact phase_graph_derivative_limit hd hH he
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_PhaseContact
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
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma coordinatePhaseFlow_of_minimizer {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    {u:M → ℝ} (hu:Continuous u) (hp:p∈minimizingVectors x)
    {t:ℝ} (ht:0<t) (ht1:t≤1)
    (he:hopfLax t u (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1=
      u x+cost x (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1/t)
    (hz:(sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1∈
      (extChartAt 𝓘(ℝ,Model n) a).source)
    (hd:MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u)
      (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1) :
    coordinatePhaseFlow a (t,
      extChartAt 𝓘(ℝ,Model n) a (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1,
      fderiv ℝ (fun z=>hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm z))
        (extChartAt 𝓘(ℝ,Model n) a (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1)) =
      phaseLower a (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M) (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)) := by
  let w:TangentBundle 𝓘(ℝ,Model n) M:=⟨x,p⟩
  let z:=sprayFlow t w
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  let η:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hf:=hopfLax_derivative_of_minimizer hu hp ht ht1 he hd
  have hf':HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u) z.1 (innerSL ℝ ((1:ℝ) • z.2)) := by
    simpa only [one_smul] using hf
  have hh:=coordinate_gradient_of_hasMFDerivAt z hz (hopfLax t u) 1 hf'
  simp only [one_smul] at hh
  have hi:=riemannianCoordinateMetric_isInvertible (χ.map_source hz)
  have hraise:phaseRaise a (χ z.1,fderiv ℝ (fun q=>hopfLax t u (χ.symm q)) (χ z.1))=η z := by
    apply Prod.ext
    · rfl
    · change (riemannianCoordinateMetric a (χ z.1)).inverse _=(η z).2
      rw [hh.fderiv,hi.inverse_apply_self]
  change phaseLower a (η (sprayFlow (-t) (η.symm (phaseRaise a
    (χ z.1,fderiv ℝ (fun q=>hopfLax t u (χ.symm q)) (χ z.1))))))=phaseLower a (η w)
  rw [hraise,η.left_inv ((tangent_chart_source_iff _ _).mpr hz)]
  rw [←sprayFlow_add,neg_add_cancel,sprayFlow_zero]

omit [Nonempty M] in
lemma divided_kernel_gradient {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    {t:ℝ} (ht:t≠0) (hp:t • p∈injectivityDomain x)
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    HasFDerivAt (fun y=>cost ((extChartAt 𝓘(ℝ,Model n) a).symm y)
      (riemannianExp x (t • p))/t)
      (-(phaseLower a (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M) (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M))).2)
      (extChartAt 𝓘(ℝ,Model n) a x) := by
  have hg:=cost_start_gradient_of_injectivityDomain hp
  have hg':HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (fun y=>cost y (riemannianExp x (t • p))) x
      (innerSL ℝ ((-t) • p)) := by simpa only [neg_smul] using hg
  have hc:=coordinate_gradient_of_hasMFDerivAt (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)
    hx (fun y=>cost y (riemannianExp x (t • p))) (-t) hg'
  simp only [div_eq_mul_inv]
  apply (hc.mul_const t⁻¹).congr_fderiv
  ext v
  simp only [smul_apply, neg_apply,smul_eq_mul,phaseLower]
  field_simp
  rfl

lemma phase_contact_semiconvex {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    {u:M → ℝ} (hu:Continuous u) (hp:p∈minimizingVectors x)
    {t:ℝ} (ht:0<t) (ht1:t<1)
    (he:hopfLax t u (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1=
      u x+cost x (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1/t)
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hz:(sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1∈
      (extChartAt 𝓘(ℝ,Model n) a).source)
    (hd:MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u)
      (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1)
    {s:Set (Model n)} {K:ℝ}
    (hxs:extChartAt 𝓘(ℝ,Model n) a x∈s)
    (hsem:ConvexOn ℝ s (fun y=>u ((extChartAt 𝓘(ℝ,Model n) a).symm y)+K/2*‖y‖^2)) :
    let Q:=coordinatePhaseFlow a (t,
      extChartAt 𝓘(ℝ,Model n) a (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1,
      fderiv ℝ (fun z=>hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm z))
        (extChartAt 𝓘(ℝ,Model n) a (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1))
    Q.1=extChartAt 𝓘(ℝ,Model n) a x ∧
      IsSemiconvexSubgradientOn (fun y=>u ((extChartAt 𝓘(ℝ,Model n) a).symm y)) s K Q.1
        ((InnerProductSpace.toDual ℝ (Model n)).symm Q.2) := by
  dsimp only
  rw [coordinatePhaseFlow_of_minimizer hu hp ht ht1.le he hz hd]
  refine ⟨rfl,?_⟩
  have hk:=divided_kernel_gradient ht.ne' (contracted_minimizer_mem_injectivityDomain hp ht ht1) hx
  have hmin:∀ᶠ y in 𝓝 (extChartAt 𝓘(ℝ,Model n) a x),
      u ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a x))+
        cost ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a x))
          (riemannianExp x (t • p))/t ≤
      u ((extChartAt 𝓘(ℝ,Model n) a).symm y)+
        cost ((extChartAt 𝓘(ℝ,Model n) a).symm y) (riemannianExp x (t • p))/t := by
    apply Eventually.of_forall
    intro y
    rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv hx,riemannianExp_smul,←he]
    exact hopfLax_le hu t _ _
  have HH:=kernel_minimum_semiconvex_subgradient hsem hxs hk hmin
  simp only [neg_neg] at HH
  convert HH using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ModifiedPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma mdifferentiable_of_fixed_chart {a z:M} {f:M → ℝ}
    (hz:z∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hd:DifferentiableAt ℝ (fun q=>f ((extChartAt 𝓘(ℝ,Model n) a).symm q))
      (extChartAt 𝓘(ℝ,Model n) a z)) :
    MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f z := by
  have H:=hd.hasFDerivAt.hasMFDerivAt.comp z
    (mdifferentiableAt_extChartAt (I:=𝓘(ℝ,Model n))
      (show z∈(chartAt (Model n) a).source from by simpa only [extChartAt_source] using hz)).hasMFDerivAt
  apply (H.congr_of_eventuallyEq ?_).mdifferentiableAt
  filter_upwards [(isOpen_extChartAt_source a).mem_nhds hz] with y hy
  simp only [Function.comp_apply,(extChartAt 𝓘(ℝ,Model n) a).left_inv hy]

lemma WeakMTW.modified_phase_subgradient (hmtw:WeakMTW (n:=n) (M:=M))
    {u v:M → ℝ} (hu:Continuous u) {L:ℝ≥0} (hv:LipschitzWith L v)
    (hdual:IsCostDualPair u v) {φ:ℝ → ℝ} (hφc:Continuous φ)
    {a y z:M} {l τ:ℝ} (hφ:HasDerivAt φ l (v y))
    (hl:0<l) (hl1:l<1) (hτ:0<τ) (hτ1:τ<1)
    (hval:hopfLax τ (fun w=>φ (v w)) z=φ (v y)+cost y z/τ)
    (hy:y∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hz:z∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hd:DifferentiableAt ℝ (fun q=>hopfLax τ (fun w=>φ (v w))
      ((extChartAt 𝓘(ℝ,Model n) a).symm q)) (extChartAt 𝓘(ℝ,Model n) a z))
    {s:Set (Model n)} {K:ℝ} (hys:extChartAt 𝓘(ℝ,Model n) a y∈s)
    (hsem:ConvexOn ℝ s (fun q=>φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))+K/2*‖q‖^2)) :
    let Q:=coordinatePhaseFlow a (τ,extChartAt 𝓘(ℝ,Model n) a z,
      fderiv ℝ (fun q=>hopfLax τ (fun w=>φ (v w)) ((extChartAt 𝓘(ℝ,Model n) a).symm q))
        (extChartAt 𝓘(ℝ,Model n) a z))
    Q.1=extChartAt 𝓘(ℝ,Model n) a y ∧
      IsSemiconvexSubgradientOn (fun q=>φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))) s K
        (extChartAt 𝓘(ℝ,Model n) a y) ((InnerProductSpace.toDual ℝ (Model n)).symm Q.2) := by
  obtain ⟨p,_,he,_,_,hp⟩:=hmtw.exists_center_ray_of_minimizer hu hv hdual hφc hφ hl hl1 hτ hτ1 hval
  have he':(sprayFlow τ (⟨y,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1=z := by
    rwa [riemannianExp_smul] at he
  have HH:=phase_contact_semiconvex (hφc.comp hv.continuous)
    (injectivityDomain_subset_minimizingVectors y hp) hτ hτ1
    (he'.symm ▸ hval) hy (he'.symm ▸ hz)
    (he'.symm ▸ mdifferentiable_of_fixed_chart hz hd) hys hsem
  rw [he'] at HH
  dsimp only at HH ⊢
  exact ⟨HH.1,HH.1 ▸ HH.2⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_JensenPhase
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.jensen_phase_graph_identity (hmtw:WeakMTW (n:=n) (M:=M))
    {u v w:M → ℝ} (hu:Continuous u) {L:ℝ≥0} (hv:LipschitzWith L v)
    (hdual:IsCostDualPair u v) {φ:ℝ → ℝ} (hφ:ContDiff ℝ ∞ φ)
    (hslope:∀y:M,0<deriv φ (v y) ∧ deriv φ (v y)<1)
    {a c:M} {N:Set (Model n)} {t:ℝ} (ht:0<t) (ht1:t<1)
    (J:JensenSamplesAt w (fun y=>φ (v y)) t a c N) (i:ℕ)
    (hi:J.z i∈(extChartAt 𝓘(ℝ,Model n) a).target)
    {p:Model n} {A:Model n →L[ℝ] Model n} {r K:ℝ} (hr:0 < r)
    (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e))
    (hexp:HasQuadraticExpansion (fun h=>φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm
      (extChartAt 𝓘(ℝ,Model n) a (J.Y (J.z i))+h)))) p A)
    (hsem:ConvexOn ℝ (Metric.ball (extChartAt 𝓘(ℝ,Model n) a (J.Y (J.z i))) r)
      (fun q=>φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))+K/2*‖q‖^2))
    (hflow:DifferentiableAt ℝ (fun q:Phase n=>coordinatePhaseFlow a (1-t,q))
      (J.z i,fderiv ℝ (chartCenterEnvelope (fun y=>φ (v y)) t a) (J.z i))) :
    (fderiv ℝ (fun q:Phase n=>coordinatePhaseFlow a (1-t,q))
      (J.z i,fderiv ℝ (chartCenterEnvelope (fun y=>φ (v y)) t a) (J.z i))).comp
      ((ContinuousLinearMap.id ℝ (Model n)).prod
        (fderiv ℝ (fderiv ℝ (chartCenterEnvelope (fun y=>φ (v y)) t a)) (J.z i)))=
      (fderiv ℝ (fun z=>extChartAt 𝓘(ℝ,Model n) a (J.Y z)) (J.z i)).prod
        (((innerSL ℝ).comp A).comp
          (fderiv ℝ (fun z=>extChartAt 𝓘(ℝ,Model n) a (J.Y z)) (J.z i))) := by
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  let G:=chartCenterEnvelope (n := n) (fun y=>φ (v y)) t a
  have hY:HasFDerivAt (fun z=>χ (J.Y z)) (fderiv ℝ (fun z=>χ (J.Y z)) (J.z i)) (J.z i) :=
    (J.samples i).2.2.2.2.1
  have hsub:∀ᶠ z in 𝓝 (J.z i),
      (coordinatePhaseFlow a (1-t,z,fderiv ℝ G z)).1=χ (J.Y z) ∧
      IsSemiconvexSubgradientOn (fun q=>φ (v (χ.symm q))) (Metric.ball (χ (J.Y (J.z i))) r) K
        (χ (J.Y z)) ((InnerProductSpace.toDual ℝ (Model n)).symm
          (coordinatePhaseFlow a (1-t,z,fderiv ℝ G z)).2) := by
    filter_upwards [J.openRegion.mem_nhds (J.sampleInRegion i),
      (isOpen_extChartAt_target a).mem_nhds hi,
      hY.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hr)] with z hz hzt hball
    have H:=hmtw.modified_phase_subgradient (s := Metric.ball (χ (J.Y (J.z i))) r) hu hv hdual hφ.continuous
      ((hφ.differentiable (by simp)).differentiableAt.hasDerivAt (x := v (J.Y z)))
      (hslope _).1 (hslope _).2 (sub_pos.mpr ht1) (by linarith : 1-t<1)
      (((J.actual z hz).2.2.1 (J.Y z)).mpr rfl) (J.actual z hz).1 (χ.map_target hzt)
      (by rw [χ.right_inv hzt]; exact J.centerDifferentiable z hz) hball hsem
    simpa only [χ, G, chartCenterEnvelope, (extChartAt 𝓘(ℝ,Model n) a).right_inv hzt] using H
  exact semiconvex_phase_graph_derivative hA hexp hr K hY
    ((J.samples i).2.2.2.2.2.2.2.2.1.hasFDerivAt) hflow.hasFDerivAt
    (hsub.mono (fun _ h=>h.1)) (hsub.mono (fun _ h=>h.2))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_JensenUndoShort
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.jensen_undo_short_oai (hmtw:WeakMTW (n:=n) (M:=M))
    {u v:M → ℝ} (hu:Continuous u) {L:ℝ≥0} (hv:LipschitzWith L v)
    (hdual:IsCostDualPair u v) {φ:ℕ → ℝ → ℝ} (hφ:∀k,ContDiff ℝ ∞ (φ k))
    (hslope:∀k,∀y:M,0<deriv (φ k) (v y) ∧ deriv (φ k) (v y)<1)
    {a:M} {N:Set (Model n)} {t:ℕ → ℝ} (ht:∀k,0<t k) (ht1:∀k,t k<1)
    {w:ℕ → M → ℝ} {c:ℕ → M}
    (J:∀k,JensenSamplesAt (w k) (fun y=>φ k (v y)) (t k) a (c k) N)
    (i:ℕ → ℕ) (hti:Tendsto t atTop (𝓝 1))
    {g:Model n →L[ℝ] ℝ} {H:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hz:Tendsto (fun k=>(J k).z (i k)) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hg:Tendsto (fun k=>fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a)
      ((J k).z (i k))) atTop (𝓝 g))
    (hH:Tendsto (fun k=>fderiv ℝ (fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a))
      ((J k).z (i k))) atTop (𝓝 H))
    (hexp:∀ᶠ k in atTop,∃p:Model n,∃A:Model n →L[ℝ] Model n,
      (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
      HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) a).symm
        (extChartAt 𝓘(ℝ,Model n) a ((J k).Y ((J k).z (i k)))+h))) p A)
    (hsem:∀ᶠ k in atTop,∃r>0,∃K:ℝ,
      ConvexOn ℝ (Metric.ball (extChartAt 𝓘(ℝ,Model n) a ((J k).Y ((J k).z (i k)))) r)
      (fun q=>φ k (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))+K/2*‖q‖^2)) :
    ∃p:ℕ → Model n,∃A:ℕ → Model n →L[ℝ] Model n,
      (∀ᶠ k in atTop,(∀d e,inner ℝ (A k d) e=inner ℝ d (A k e)) ∧
        HasQuadraticExpansion (fun h=>φ k (v ((extChartAt 𝓘(ℝ,Model n) a).symm
          (extChartAt 𝓘(ℝ,Model n) a ((J k).Y ((J k).z (i k)))+h)))) (p k) (A k)) ∧
      Tendsto (fun k=>(innerSL ℝ).comp (A k)) atTop (𝓝 H) ∧
      Tendsto (fun k=>fderiv ℝ (fun z=>extChartAt 𝓘(ℝ,Model n) a ((J k).Y z))
        ((J k).z (i k))) atTop (𝓝 1) := by
  classical
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  let P:=fun k (p:Model n) (A:Model n →L[ℝ] Model n)=>
    (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
      HasQuadraticExpansion (fun h=>φ k (v (χ.symm (χ ((J k).Y ((J k).z (i k)))+h)))) p A
  have hP:∀ᶠ k in atTop,∃p A,P k p A := by
    filter_upwards [hexp] with k hk
    obtain ⟨p,A,hs,hA⟩:=hk
    exact quadratic_expansion_scalar_exists hA ((hφ k).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top : (2:WithTop ℕ∞)≤∞))
  have hchoice:∀k,∃p A,(∃p A,P k p A) → P k p A := by
    intro k
    by_cases hk:∃p A,P k p A
    · obtain ⟨p,A,h⟩:=hk
      exact ⟨p,A,fun _=>h⟩
    · exact ⟨0,0,fun h=>False.elim (hk h)⟩
  choose p A hPA using hchoice
  have hPA':∀ᶠ k in atTop,P k (p k) (A k):=hP.mono (fun k hk=>hPA k hk)
  have hτ:Tendsto (fun k=>1-t k) atTop (𝓝 (0:ℝ)):=by
    simpa only [sub_self] using (tendsto_const_nhds.sub hti : Tendsto (fun k=>(1:ℝ)-t k) atTop (𝓝 (1-1)))
  have hq:Tendsto (fun k=>((J k).z (i k),fderiv ℝ
      (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a) ((J k).z (i k))))
      atTop (𝓝 (χ a,g)):=hz.prodMk_nhds hg
  have hflow:∀ᶠ k in atTop,DifferentiableAt ℝ
      (fun q:Phase n=>coordinatePhaseFlow a (1-t k,q))
      ((J k).z (i k),fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a) ((J k).z (i k))) := by
    have HH:=((coordinatePhaseFlow_contDiffAt (q := (χ a,g))
      (mem_extChartAt_target (I := 𝓘(ℝ,Model n)) a)).of_le
        (by norm_num : (1:WithTop ℕ∞)≤∞)).eventually (by norm_num)
    filter_upwards [(hτ.prodMk_nhds hq).eventually HH] with k hk
    exact (hk.differentiableAt (by norm_num)).comp _
      ((contDiffAt_const.prodMk contDiffAt_id : ContDiffAt ℝ 1 (fun q:Phase n=>(1-t k,q)) _).differentiableAt (by norm_num))
  have hi:∀ᶠ k in atTop,(J k).z (i k)∈χ.target:=
    hz.eventually ((isOpen_extChartAt_target a).mem_nhds (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a))
  have hid:∀ᶠ k in atTop,
      (fderiv ℝ (fun q:Phase n=>coordinatePhaseFlow a (1-t k,q))
        ((J k).z (i k),fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a) ((J k).z (i k)))).comp
          ((ContinuousLinearMap.id ℝ (Model n)).prod
            (fderiv ℝ (fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (t k) a)) ((J k).z (i k))))=
      (fderiv ℝ (fun z=>χ ((J k).Y z)) ((J k).z (i k))).prod
        (((innerSL ℝ).comp (A k)).comp (fderiv ℝ (fun z=>χ ((J k).Y z)) ((J k).z (i k)))) := by
    filter_upwards [hi,hPA',hsem,hflow] with k hik hk hs hf
    obtain ⟨r,hr,K,hK⟩:=hs
    exact hmtw.jensen_phase_graph_identity hu hv hdual (hφ k) (hslope k) (ht k) (ht1 k)
      (J k) (i k) hik hr hk.1 hk.2 hK hf
  have HH:=coordinate_phase_jet_limit (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a) hτ hq hH hid
  exact ⟨p,A,hPA',HH.2,HH.1⟩
end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.jensen_undo_short_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.jensen_undo_short_oai.{u_1}
