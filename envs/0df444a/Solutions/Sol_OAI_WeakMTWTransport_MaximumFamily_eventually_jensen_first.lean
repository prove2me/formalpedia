-- Prove2me | solution 1 for OAI.WeakMTWTransport.MaximumFamily.eventually_jensen_first
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:42:53.993198+00:00
-- url     : https://prove2.me/submissions/f117ec73-a2ad-4f68-8e0b-25e003f89bef

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
import Theorems.Thm_OAI_WeakMTWTransport_MaximumRow_jensen_first_limit
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_family_comparison_local_data

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_FullSet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma HasSecondTaylor.add {f g : E → ℝ} {l k : E →L[ℝ] ℝ}
    {B C : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B)
    (hg : HasSecondTaylor g k C) : HasSecondTaylor (fun h => f h+g h) (l+k) (B+C) := by
  unfold HasSecondTaylor at *
  have he : (fun h => (f h+g h)-(f 0+g 0)-(l+k) h-(B+C) h h/2) =
      (fun h => (f h-f 0-l h-B h h/2)+(g h-g 0-k h-C h h/2)) := by
    funext h
    simp only [_root_.add_apply]
    ring
  rw [he]
  exact Asymptotics.IsLittleO.add hf hg

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_JensenMaximum
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
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma jensen_C11_select {f : E → ℝ} {g : E → E} {x0 : E} {r eta : ℝ}
    {L : ℝ≥0} (hr : 0 < r) (heta : 0 < eta)
    (hf : ContinuousOn f (Metric.closedBall x0 r))
    (hmax : ∀ x ∈ Metric.closedBall x0 r, f x ≤ f x0)
    (hd : ∀ x ∈ Metric.ball x0 r, HasFDerivAt f ((innerSL ℝ) (g x)) x)
    (hlip : LipschitzOnWith L g (Metric.closedBall x0 r))
    (μ : Measure E) [μ.IsAddHaarMeasure] {P : E → Prop} (hP : ∀ᵐ z ∂μ, P z) :
    ∃ z ∈ Metric.ball x0 r, P z ∧ ‖g z‖ ≤ 2*eta*r ∧
      ∀ x ∈ Metric.closedBall x0 r,
        f x ≤ f z + inner ℝ (g z) (x-z) + eta/2*‖x-z‖^2 := by
  let nu : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  let psi : E → E := fun x => g x - eta • (x-x0)
  let N : Set E := Metric.closedBall x0 r ∩ {x | ¬P x}
  have hN : μ N = 0 := measure_mono_null inter_subset_right (ae_iff.mp hP)
  have hNnu : nu N = 0 := (Measure.absolutelyContinuous_isAddHaarMeasure nu μ) hN
  have hpsi : LipschitzOnWith (L+⟨eta,heta.le⟩) psi (Metric.closedBall x0 r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have heq : psi x - psi y = (g x-g y)-eta • (x-y) := by
      dsimp [psi]
      simp only [smul_sub]
      abel
    rw [dist_eq_norm,heq]
    calc
      ‖(g x-g y)-eta • (x-y)‖ ≤ ‖g x-g y‖+‖eta • (x-y)‖ := norm_sub_le _ _
      _ ≤ L * dist x y + eta * dist x y := by
        simp only [norm_smul_of_nonneg heta.le,← dist_eq_norm]
        exact add_le_add (hlip.dist_le_mul x hx y hy) le_rfl
      _ = (↑(L+⟨eta,heta.le⟩) : ℝ) * dist x y := by change (L:ℝ)*dist x y+eta*dist x y=((L:ℝ)+eta)*dist x y; ring
  have hnullnu : nu (psi '' N) = 0 := by
    have hh := (hpsi.mono (show N ⊆ Metric.closedBall x0 r from inter_subset_left)).hausdorffMeasure_image_le
      (by positivity : (0:ℝ) ≤ Module.finrank ℝ E)
    simpa only [nu,hNnu,mul_zero,nonpos_iff_eq_zero] using hh
  have hnull : μ (psi '' N) = 0 :=
    (Measure.absolutelyContinuous_isAddHaarMeasure μ nu) hnullnu
  have hdense : Dense {a | a ∉ psi '' N} := μ.dense_of_ae
    (ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using hnull))
  obtain ⟨a,ha,han⟩ := hdense.inter_open_nonempty (Metric.ball 0 (eta*r/4))
    Metric.isOpen_ball (Metric.nonempty_ball.mpr (by positivity))
  have hanorm : ‖a‖ < eta*r/4 := by simpa only [Metric.mem_ball,dist_zero_right] using ha
  let F : E → ℝ := fun x => f x - eta/2*‖x-x0‖^2-inner ℝ a (x-x0)
  have hFc : ContinuousOn F (Metric.closedBall x0 r) := by
    exact (hf.sub (by fun_prop)).sub (by fun_prop)
  obtain ⟨z,hz,hzmax⟩ := (isCompact_closedBall x0 r).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr hr.le) hFc
  have hcenter : F x0 ≤ F z := hzmax (Metric.mem_closedBall_self hr.le)
  have hzb : z ∈ Metric.ball x0 r := by
    have hzn : ‖z-x0‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have hlin := abs_real_inner_le_norm a (z-x0)
    have hz0 := hmax z hz
    have hanon : -‖a‖*‖z-x0‖ ≤ inner ℝ a (z-x0) := by
      have hh := (abs_le.mp hlin).1
      nlinarith
    by_contra hn
    have hzeq : ‖z-x0‖ = r := by
      have hh : r ≤ ‖z-x0‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hn
      exact le_antisymm hzn hh
    dsimp [F] at hcenter
    simp only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,inner_zero_right,sub_zero] at hcenter
    rw [hzeq] at hcenter hanon
    have hh : ‖a‖*r < eta*r^2/4 := by nlinarith
    have hpos : 0 < eta*r^2 := mul_pos heta (sq_pos_of_pos hr)
    nlinarith
  have hdF : HasFDerivAt F ((innerSL ℝ) (psi z-a)) z := by
    have hdq : HasFDerivAt (fun x:E => eta/2*‖x-x0‖^2)
        ((eta/2) • (2 • ((innerSL ℝ) (z-x0)))) z := by
      simpa only [id_eq,ContinuousLinearMap.comp_id] using
        ((((hasFDerivAt_id (𝕜 := ℝ) z).sub_const x0).norm_sq).const_mul (eta/2))
    have hda : HasFDerivAt (fun x:E => inner ℝ a (x-x0)) ((innerSL ℝ) a) z := by
      simpa only [id_eq,ContinuousLinearMap.comp_id,Function.comp_def,innerSL_apply_apply] using
        (((innerSL ℝ) a).hasFDerivAt.comp z
          ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const x0))
    apply (((hd z hzb).sub hdq).sub hda).congr_fderiv
    ext h
    simp only [psi,sub_apply,smul_apply,innerSL_apply_apply,inner_sub_left,real_inner_smul_left]
    ring
  have hzero := (hzmax.isLocalMax (mem_of_superset
    (Metric.isOpen_ball.mem_nhds hzb) Metric.ball_subset_closedBall)).hasFDerivAt_eq_zero hdF
  have hpsia : psi z = a := by
    have heval := congrArg (fun A : E →L[ℝ] ℝ => A (psi z-a)) hzero
    simp only [innerSL_apply_apply,zero_apply,real_inner_self_eq_norm_sq] at heval
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp heval))
  have hzP : P z := by
    by_contra hn
    exact han ⟨z,⟨hz,hn⟩,hpsia⟩
  have hg : g z = eta • (z-x0)+a := by
    dsimp [psi] at hpsia
    exact (sub_eq_iff_eq_add.mp hpsia).trans (add_comm _ _)
  refine ⟨z,hzb,hzP,?_,?_⟩
  · have hzn : ‖z-x0‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hzb
    calc
      ‖g z‖ ≤ eta*‖z-x0‖+‖a‖ := by rw [hg]; simpa only [norm_smul_of_nonneg heta.le] using norm_add_le (eta • (z-x0)) a
      _ ≤ 2*eta*r := by nlinarith
  · intro x hx
    have hm := hzmax hx
    have hnorm : ‖x-x0‖^2 = ‖x-z‖^2+2*inner ℝ (x-z) (z-x0)+‖z-x0‖^2 := by
      have heq : x-x0 = (x-z)+(z-x0) := by abel
      rw [heq]
      simp only [← real_inner_self_eq_norm_sq,inner_add_left,inner_add_right]
      have hcom : inner ℝ (z-x0) (x-z) = inner ℝ (x-z) (z-x0) := real_inner_comm _ _
      rw [hcom]
      ring
    have hinner : inner ℝ a (x-x0) = inner ℝ a (x-z)+inner ℝ a (z-x0) := by
      rw [show x-x0 = (x-z)+(z-x0) by abel,inner_add_right]
    dsimp [F] at hm
    rw [hnorm,hinner] at hm
    rw [hg,inner_add_left,real_inner_smul_left]
    have hcom : inner ℝ (x-z) (z-x0) = inner ℝ (z-x0) (x-z) := real_inner_comm _ _
    rw [hcom] at hm
    linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ModifiedEnvelopeRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma HasSecondTaylor.hasQuadraticExpansion {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) :
    HasQuadraticExpansion f ((InnerProductSpace.toDual ℝ E).symm l) (bilinearOperator B) := by
  intro ε hε
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (hf.eventually hε)
  refine ⟨r,hr,?_⟩
  intro h hh
  have H := hball (by simpa only [mem_ball,dist_zero_right] using hh)
  simpa only [quadraticTaylor,bilinearOperator_inner,InnerProductSpace.toDual_symm_apply,
    sub_add_eq_sub_sub] using H

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

lemma ae_secondTaylor_of_C11 {f : E → ℝ} {S : Set E} (hS : IsOpen S)
    (hd : ∀ x∈S,DifferentiableAt ℝ f x) {K : ℝ≥0}
    (hK : LipschitzOnWith K (fderiv ℝ f) S) :
    ∀ᵐ x ∂μ,x∈S → DifferentiableAt ℝ (fderiv ℝ f) x ∧
      HasSecondTaylor (fun h => f (x+h)) (fderiv ℝ f x)
        (fderiv ℝ (fderiv ℝ f) x) := by
  filter_upwards [hK.ae_differentiableWithinAt_of_mem (μ := μ)] with x hx hxS
  have H := (hx hxS).differentiableAt (hS.mem_nhds hxS)
  refine ⟨H,hasSecondTaylor_of_second_derivative ?_ H.hasFDerivAt⟩
  filter_upwards [hS.mem_nhds hxS] with y hy
  exact (hd y hy).hasFDerivAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Taylor
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

lemma HasQuadraticExpansion.hessian_le_of_upper_support {f : E → ℝ} {p : E}
    {A : E →L[ℝ] E} (hexp : HasQuadraticExpansion f p A) {eta R : ℝ}
    (hR : 0 < R)
    (hu : ∀ h : E, ‖h‖ < R →
      f h ≤ f 0+inner ℝ p h+eta/2*‖h‖^2) :
    ∀ e : E, inner ℝ (A e) e ≤ eta*‖e‖^2 := by
  intro e
  have hbound (eps : ℝ) (heps : 0 < eps) :
      inner ℝ (A e) e ≤ (eta+2*eps)*‖e‖^2 := by
    obtain ⟨d,hd,hrem⟩ := hexp eps heps
    let t : ℝ := min R d / (2*(‖e‖+1))
    have ht : 0 < t := by dsimp [t] <;> positivity
    have hteq : t*(2*(‖e‖+1)) = min R d :=
      div_mul_cancel₀ _ (by positivity)
    have htn : t*‖e‖ < min R d := by nlinarith [norm_nonneg e]
    have hnorm : ‖t • e‖ = t*‖e‖ := norm_smul_of_nonneg ht.le _
    have hi := hu (t • e) (by rw [hnorm]; exact lt_of_lt_of_le htn (min_le_left _ _))
    have hr := (abs_le.mp (hrem (t • e) (by
      rw [hnorm]; exact lt_of_lt_of_le htn (min_le_right _ _)))).1
    simp only [quadraticTaylor,map_smul,real_inner_smul_left,real_inner_smul_right,hnorm] at hr hi
    have hscale : t^2 * inner ℝ (A e) e ≤ t^2 * ((eta+2*eps)*‖e‖^2) := by
      nlinarith
    nlinarith [sq_pos_of_pos ht]
  have hcl : (0:ℝ) ∈ closure (Ioo 0 1) := by
    rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
    exact ⟨le_rfl,zero_le_one⟩
  have hc : Continuous (fun eps : ℝ => (eta+2*eps)*‖e‖^2) := by fun_prop
  have hh := ContinuousWithinAt.closure_le hcl
    (continuousWithinAt_const (b := inner ℝ (A e) e)) hc.continuousWithinAt
    (fun eps heps => hbound eps heps.1)
  simpa only [mul_zero,add_zero] using hh

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_ContactJacobianMeasure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma measure_eq_zero_of_nonsingular_null_image {f : E → E} {df : E → E →L[ℝ] E}
    {s : Set E} (hd : ∀ x∈s, HasFDerivWithinAt f (df x) s x)
    (hdet : ∀ x∈s, (df x).det≠0) (hnull : μ (f '' s)=0) : μ s=0 := by
  classical
  have hchoice : ∀ A : E →L[ℝ] E, ∃ δ : ℝ≥0, 0<δ ∧
      (A.det≠0 → ∀ a : Set E, ∀ g : E → E,
        ApproximatesLinearOn g A a δ → μ (g '' a)=0 → μ a=0) := by
    intro A
    by_cases hA : A.det=0
    · exact ⟨1,zero_lt_one,fun h => (h hA).elim⟩
    have ha : 0 < |A.det| := abs_pos.mpr hA
    let m : ℝ≥0 := ⟨|A.det|/2,by positivity⟩
    have hm : (m:ℝ≥0∞)<ENNReal.ofReal |A.det| := by
      rw [ENNReal.ofReal_eq_coe_nnreal,ENNReal.coe_lt_coe]
      change m < ⟨|A.det|, abs_nonneg _⟩
      exact_mod_cast (half_lt_self ha)
    have hpos : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), 0<δ := self_mem_nhdsWithin
    obtain ⟨δ,hδ,H⟩ := (hpos.and (mul_le_addHaar_image_of_lt_det μ A hm)).exists
    refine ⟨δ,hδ,fun _ a g hg hz => ?_⟩
    have hh : (m:ℝ≥0∞)*μ a=0 := le_antisymm ((H a g hg).trans_eq hz) bot_le
    have hmpos : (0:ℝ≥0∞) < m := by
      exact_mod_cast (show (0:ℝ)<(m:ℝ) by change 0 < |A.det| / 2; exact half_pos ha)
    exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt hmpos)
  choose δ hδ Hδ using hchoice
  obtain ⟨t,A,_,hcover,happrox,hA⟩ :=
    exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt f s df hd δ
      (fun A => (hδ A).ne')
  rcases s.eq_empty_or_nonempty with rfl|hs
  · exact measure_empty
  have ht : ∀ k, μ (s∩t k)=0 := by
    intro k
    obtain ⟨y,hy,hAy⟩ := hA hs k
    apply Hδ (A k) (hAy ▸ hdet y hy) (s∩t k) f (happrox k)
    exact measure_mono_null (Set.image_mono inter_subset_left) hnull
  apply measure_mono_null (t := ⋃ k, s∩t k)
  · intro x hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨k,hx,hk⟩
  · exact measure_iUnion_null ht

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_JensenNullPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma ae_nonsingular_map_avoids_null {Y : E → E} {D : E → E →L[ℝ] E}
    {N : Set E} (hN : μ N=0) :
    ∀ᵐ z ∂μ,HasFDerivAt Y (D z) z → (D z).det≠0 → Y z∉N := by
  let Z := {z | HasFDerivAt Y (D z) z ∧ (D z).det≠0 ∧ Y z∈N}
  have hZ : μ Z=0 := measure_eq_zero_of_nonsingular_null_image μ
    (fun z hz => hz.1.hasFDerivWithinAt) (fun z hz => hz.2.1)
    (measure_mono_null (by rintro _ ⟨z,hz,rfl⟩; exact hz.2.2) hN)
  have H : ∀ᵐ z ∂μ,z∉Z := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hZ
  filter_upwards [H] with z hz hd hdet hmem
  exact hz ⟨hd,hdet,hmem⟩
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_SimultaneousC11Jensen
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma simultaneous_C11_jensen {f k : E → ℝ} {Y Z : E → E}
    {S : Set E} (hS : IsOpen S) {x0 : E} {r eta : ℝ}
    (hr : 0 < r) (heta : 0<eta) (hsub : closedBall x0 r⊆S)
    (hf : ∀ x∈S,DifferentiableAt ℝ f x)
    (hk : ∀ x∈S,DifferentiableAt ℝ k x)
    {Lf Lk LY LZ : ℝ≥0}
    (hfl : LipschitzOnWith Lf (fderiv ℝ f) S)
    (hkl : LipschitzOnWith Lk (fderiv ℝ k) S)
    (hY : LipschitzOnWith LY Y S) (hZ : LipschitzOnWith LZ Z S)
    (hmax : ∀ x∈closedBall x0 r,f x+k x≤f x0+k x0)
    {N : Set E} (hN : μ N=0) {P : E → Prop}
    (hP : ∀ᵐ z ∂μ,z∈S → P z) :
    ∃ z∈ball x0 r,P z ∧
      HasFDerivAt Y (fderiv ℝ Y z) z ∧ HasFDerivAt Z (fderiv ℝ Z z) z ∧
      ((fderiv ℝ Y z).det≠0 → Y z∉N) ∧
      HasSecondTaylor (fun h => f (z+h)) (fderiv ℝ f z) (fderiv ℝ (fderiv ℝ f) z) ∧
      HasSecondTaylor (fun h => k (z+h)) (fderiv ℝ k z) (fderiv ℝ (fderiv ℝ k) z) ∧
      ‖fderiv ℝ f z+fderiv ℝ k z‖≤2*eta*r ∧
      ∀ e:E,fderiv ℝ (fderiv ℝ f) z e e+fderiv ℝ (fderiv ℝ k) z e e≤eta*‖e‖^2 := by
  let g : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm
    (fderiv ℝ f x+fderiv ℝ k x)
  have hlip : LipschitzOnWith (Lf+Lk) g (closedBall x0 r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change dist ((InnerProductSpace.toDual ℝ E).symm _)
      ((InnerProductSpace.toDual ℝ E).symm _)≤_
    rw [(InnerProductSpace.toDual ℝ E).symm.isometry.dist_eq]
    exact ((hfl.add hkl).mono hsub).dist_le_mul x hx y hy
  have hd : ∀ x∈ball x0 r,
      HasFDerivAt (fun x => f x+k x) ((innerSL ℝ) (g x)) x := by
    intro x hx
    have HH := (hf x (hsub (ball_subset_closedBall hx))).hasFDerivAt.add
      (hk x (hsub (ball_subset_closedBall hx))).hasFDerivAt
    have hg : (innerSL ℝ) (g x)=fderiv ℝ f x+fderiv ℝ k x :=
      (InnerProductSpace.toDual ℝ E).apply_symm_apply _
    rwa [hg]
  have hc : ContinuousOn (fun x => f x+k x) (closedBall x0 r) :=
    fun x hx => ((hf x (hsub hx)).continuousAt.add (hk x (hsub hx)).continuousAt).continuousWithinAt
  have H : ∀ᵐ z ∂μ,z∈ball x0 r → P z ∧
      HasFDerivAt Y (fderiv ℝ Y z) z ∧ HasFDerivAt Z (fderiv ℝ Z z) z ∧
      ((fderiv ℝ Y z).det≠0 → Y z∉N) ∧
      HasSecondTaylor (fun h => f (z+h)) (fderiv ℝ f z) (fderiv ℝ (fderiv ℝ f) z) ∧
      HasSecondTaylor (fun h => k (z+h)) (fderiv ℝ k z) (fderiv ℝ (fderiv ℝ k) z) := by
    filter_upwards [hP,ae_secondTaylor_of_C11 μ hS hf hfl,
      ae_secondTaylor_of_C11 μ hS hk hkl,
      hY.ae_differentiableWithinAt_of_mem (μ := μ),
      hZ.ae_differentiableWithinAt_of_mem (μ := μ),
      ae_nonsingular_map_avoids_null (D := fderiv ℝ Y) μ hN]
      with z hzP hzf hzk hzY hzZ hzN hzb
    have hzS := hsub (ball_subset_closedBall hzb)
    have hyD := ((hzY hzS).differentiableAt (hS.mem_nhds hzS)).hasFDerivAt
    exact ⟨hzP hzS,hyD,((hzZ hzS).differentiableAt (hS.mem_nhds hzS)).hasFDerivAt,
      hzN hyD,(hzf hzS).2,(hzk hzS).2⟩
  obtain ⟨z,hz,hby,hgz,hu⟩ := jensen_C11_select hr heta hc hmax hd hlip μ H
  obtain ⟨hzP,hzY,hzZ,hzN,hzf,hzk⟩ := hby hz
  refine ⟨z,hz,hzP,hzY,hzZ,hzN,hzf,hzk,?_,?_⟩
  · simpa only [g,(InnerProductSpace.toDual ℝ E).symm.norm_map] using hgz
  · have hA := (hzf.add hzk).hasQuadraticExpansion
    have hzn : ‖z-x0‖ < r := by simpa only [mem_ball,dist_eq_norm] using hz
    have HA := hA.hessian_le_of_upper_support (sub_pos.mpr hzn) (by
      intro h hh
      have hdist : z+h∈closedBall x0 r := by
        rw [mem_closedBall,dist_eq_norm]
        have heq : z+h-x0=(z-x0)+h := by abel
        rw [heq]
        exact (norm_add_le _ _).trans (by linarith)
      simpa only [add_zero,add_sub_cancel_left,g] using hu (z+h) hdist)
    simpa only [bilinearOperator_inner,add_apply] using HA

lemma simultaneous_C11_jensen_near {f k : E → ℝ} {Y Z : E → E}
    {S : Set E} (hS : IsOpen S) {x0 : E} (hx : x0∈S)
    (hf : ∀ x∈S,DifferentiableAt ℝ f x)
    (hk : ∀ x∈S,DifferentiableAt ℝ k x)
    {Lf Lk LY LZ : ℝ≥0}
    (hfl : LipschitzOnWith Lf (fderiv ℝ f) S)
    (hkl : LipschitzOnWith Lk (fderiv ℝ k) S)
    (hY : LipschitzOnWith LY Y S) (hZ : LipschitzOnWith LZ Z S)
    (hmax : ∀ᶠ x in 𝓝 x0,f x+k x≤f x0+k x0)
    {N : Set E} (hN : μ N=0) {P : E → Prop}
    (hP : ∀ᵐ z ∂μ,z∈S → P z) {rho eta : ℝ} (hrho : 0 < rho) (heta : 0<eta) :
    ∃ z∈ball x0 rho,P z ∧
      HasFDerivAt Y (fderiv ℝ Y z) z ∧ HasFDerivAt Z (fderiv ℝ Z z) z ∧
      ((fderiv ℝ Y z).det≠0 → Y z∉N) ∧
      HasSecondTaylor (fun h => f (z+h)) (fderiv ℝ f z) (fderiv ℝ (fderiv ℝ f) z) ∧
      HasSecondTaylor (fun h => k (z+h)) (fderiv ℝ k z) (fderiv ℝ (fderiv ℝ k) z) ∧
      ‖fderiv ℝ f z+fderiv ℝ k z‖≤eta ∧
      ∀ e:E,fderiv ℝ (fderiv ℝ f) z e e+fderiv ℝ (fderiv ℝ k) z e e≤eta*‖e‖^2 := by
  obtain ⟨R,hR,HR⟩ := Metric.eventually_nhds_iff.mp
    (hmax.and (hS.mem_nhds hx))
  let r := min (R/2) (min rho (1/2))
  have hr : 0 < r := lt_min (by positivity) (lt_min hrho (by norm_num))
  have hrR : r<R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrrho : r ≤ rho := (min_le_right _ _).trans (min_le_left _ _)
  have hrhalf : r≤1/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hlocal : ∀ z∈closedBall x0 r,f z+k z≤f x0+k x0 ∧ z∈S := by
    intro z hz
    exact HR (lt_of_le_of_lt (mem_closedBall.mp hz) hrR)
  obtain ⟨z,hz,hp,hy,hzD,hn,htf,htk,hg,hh⟩ := simultaneous_C11_jensen μ hS
    hr heta (fun z hz => (hlocal z hz).2) hf hk hfl hkl hY hZ
    (fun z hz => (hlocal z hz).1) hN hP
  refine ⟨z,ball_subset_ball hrrho hz,hp,hy,hzD,hn,htf,htk,hg.trans ?_,hh⟩
  nlinarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_C11HessianLimits
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_C11_hessian_limit_samples {f g : E → ℝ} {S : Set E}
    (hS : IsOpen S) {x0 : E} {Lf Lg : ℝ≥0}
    (hf : LipschitzOnWith Lf (fderiv ℝ f) S)
    (hg : LipschitzOnWith Lg (fderiv ℝ g) S) {P : E → Prop}
    (hselect : ∀ rho eta : ℝ, 0 < rho → 0 < eta → ∃ z∈S,
      dist z x0 < rho ∧ P z ∧ ‖fderiv ℝ f z+fderiv ℝ g z‖≤eta ∧
      ∀ e:E, fderiv ℝ (fderiv ℝ f) z e e+fderiv ℝ (fderiv ℝ g) z e e≤eta*‖e‖^2) :
    ∃ z : ℕ → E, ∃ A B : E →L[ℝ] E →L[ℝ] ℝ,
      (∀ i,z i∈S ∧ P (z i)) ∧ Tendsto z atTop (𝓝 x0) ∧
      Tendsto (fun i => fderiv ℝ (fderiv ℝ f) (z i)) atTop (𝓝 A) ∧
      Tendsto (fun i => fderiv ℝ (fderiv ℝ g) (z i)) atTop (𝓝 B) ∧
      Tendsto (fun i => fderiv ℝ f (z i)+fderiv ℝ g (z i)) atTop (𝓝 0) ∧
      ∀ e:E,A e e+B e e≤0 := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let eps := fun i:ℕ => 1/((i:ℝ)+1)
  have heps : ∀ i,0 < eps i := fun i => by dsimp [eps] <;> positivity
  have heps0 : Tendsto eps atTop (𝓝 (0:ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose z hzS hdist hzP hgrad hquad using fun i => hselect (eps i) (eps i) (heps i) (heps i)
  let A := fun i => fderiv ℝ (fderiv ℝ f) (z i)
  let B := fun i => fderiv ℝ (fderiv ℝ g) (z i)
  have hA : ∀ i,‖A i‖≤Lf := fun i => norm_fderiv_le_of_lipschitzOn ℝ (hS.mem_nhds (hzS i)) hf
  have hB : ∀ i,‖B i‖≤Lg := fun i => norm_fderiv_le_of_lipschitzOn ℝ (hS.mem_nhds (hzS i)) hg
  have hcompact : IsCompact ((closedBall (0 : E →L[ℝ] E →L[ℝ] ℝ) (Lf:ℝ)).prod
      (closedBall (0 : E →L[ℝ] E →L[ℝ] ℝ) (Lg:ℝ))) := (isCompact_closedBall (0 : E →L[ℝ] E →L[ℝ] ℝ) (Lf:ℝ)).prod
    (isCompact_closedBall (0 : E →L[ℝ] E →L[ℝ] ℝ) (Lg:ℝ))
  obtain ⟨AB,hAB,σ,hσ,hlim⟩ := hcompact.tendsto_subseq (x := fun i => (A i,B i))
    (fun i => by
      change dist (A i) 0≤(Lf:ℝ) ∧ dist (B i) 0≤(Lg:ℝ)
      simpa only [dist_zero_right] using And.intro (hA i) (hB i))
  have hzlim : Tendsto z atTop (𝓝 x0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp heps0).2 ε hε] with i hi
    exact (hdist i).trans hi
  have hgradlim : Tendsto (fun i => fderiv ℝ f (z i)+fderiv ℝ g (z i)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hgrad heps0
  have hlimA : Tendsto (fun i => A (σ i)) atTop (𝓝 AB.1) := by
    simpa only [Function.comp_def] using (continuous_fst.tendsto AB).comp hlim
  have hlimB : Tendsto (fun i => B (σ i)) atTop (𝓝 AB.2) := by
    simpa only [Function.comp_def] using (continuous_snd.tendsto AB).comp hlim
  refine ⟨z ∘ σ,AB.1,AB.2,fun i => ⟨hzS (σ i),hzP (σ i)⟩,
    hzlim.comp hσ.tendsto_atTop,hlimA,hlimB,hgradlim.comp hσ.tendsto_atTop,?_⟩
  intro e
  have heval : Continuous (fun J : E →L[ℝ] E →L[ℝ] ℝ => J e e) :=
    (continuous_id.clm_apply (continuous_const (y := e))).clm_apply (continuous_const (y := e))
  have ha : Tendsto (fun i => A (σ i) e e) atTop (𝓝 (AB.1 e e)) := by
    simpa only [Function.comp_def] using (heval.tendsto AB.1).comp hlimA
  have hb : Tendsto (fun i => B (σ i) e e) atTop (𝓝 (AB.2 e e)) := by
    simpa only [Function.comp_def] using (heval.tendsto AB.2).comp hlimB
  have he : Tendsto (fun i => eps (σ i)*‖e‖^2) atTop (𝓝 (0:ℝ)) := by
    simpa only [zero_mul,Function.comp_def] using (heps0.comp hσ.tendsto_atTop).mul_const (‖e‖^2)
  exact le_of_tendsto_of_tendsto (ha.add hb) he (Filter.Eventually.of_forall (fun i => hquad (σ i) e))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_JensenAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma jensen_samples_at {v g : M → ℝ} {t : ℝ} {a c : M}
    {S : Set (Model n)} (hS : IsOpen S) (hz0 : extChartAt 𝓘(ℝ,Model n) a c∈S)
    {Y : Model n → M} {JF JG JY JP : ℝ≥0}
    (hF : ∀ z∈S,DifferentiableAt ℝ (chartOuterEnvelope v t a) z)
    (hG : ∀ z∈S,DifferentiableAt ℝ (chartCenterEnvelope g t a) z)
    (hFL : LipschitzOnWith JF (fderiv ℝ (chartOuterEnvelope v t a)) S)
    (hGL : LipschitzOnWith JG (fderiv ℝ (chartCenterEnvelope g t a)) S)
    (hYL : LipschitzOnWith JY (fun z=>extChartAt 𝓘(ℝ,Model n) a (Y z)) S)
    (hPL : LipschitzOnWith JP (fun z=>extChartAt 𝓘(ℝ,Model n)
      (chartActualPole v t a (extChartAt 𝓘(ℝ,Model n) a c)) (chartActualPole v t a z)) S)
    (hactual : ∀ z∈S,
      let χ := extChartAt 𝓘(ℝ,Model n) a
      let P : Model n → M := chartActualPole v t a
      let χP := extChartAt 𝓘(ℝ,Model n) (P (χ c))
      Y z∈χ.source ∧ P z∈χP.source ∧
      (∀ y:M,chartCenterEnvelope g t a z=g y+cost y (χ.symm z)/(1-t) ↔ y=Y z) ∧
      chartOuterEnvelope v t a z=cTransform v (P z)+cost (P z) (χ.symm z)/t)
    (hmax : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ,Model n) a c),
      chartOuterEnvelope v t a z+chartCenterEnvelope g t a z≤
      chartOuterEnvelope v t a (extChartAt 𝓘(ℝ,Model n) a c)+
        chartCenterEnvelope g t a (extChartAt 𝓘(ℝ,Model n) a c))
    {N : Set (Model n)} (hN : volume N=0) : Nonempty (JensenSamplesAt (n := n) v g t a c N) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let F : Model n → ℝ := chartOuterEnvelope v t a
  let G : Model n → ℝ := chartCenterEnvelope g t a
  let P : Model n → M := chartActualPole v t a
  let χP := extChartAt 𝓘(ℝ,Model n) (P (χ c))
  let R := fun z:Model n=>
    Y z∈χ.source ∧ P z∈χP.source ∧
    (∀ y:M,G z=g y+cost y (χ.symm z)/(1-t) ↔ y=Y z) ∧
    F z=cTransform v (P z)+cost (P z) (χ.symm z)/t ∧
    HasFDerivAt (fun q=>χ (Y q)) (fderiv ℝ (fun q=>χ (Y q)) z) z ∧
    HasFDerivAt (fun q=>χP (P q)) (fderiv ℝ (fun q=>χP (P q)) z) z ∧
    ((fderiv ℝ (fun q=>χ (Y q)) z).det≠0 → χ (Y z)∉N) ∧
    DifferentiableAt ℝ (fderiv ℝ F) z ∧ DifferentiableAt ℝ (fderiv ℝ G) z ∧
    HasSecondTaylor (fun h=>F (z+h)) (fderiv ℝ F z) (fderiv ℝ (fderiv ℝ F) z) ∧
    HasSecondTaylor (fun h=>G (z+h)) (fderiv ℝ G z) (fderiv ℝ (fderiv ℝ G) z)
  have hselect : ∀ rho eta:ℝ,0 < rho → 0<eta → ∃ z∈S,
      dist z (χ c) < rho ∧ R z ∧ ‖fderiv ℝ F z+fderiv ℝ G z‖≤eta ∧
      ∀ e:Model n,fderiv ℝ (fderiv ℝ F) z e e+fderiv ℝ (fderiv ℝ G) z e e≤eta*‖e‖^2 := by
    intro rho eta hrho heta
    have haF := ae_secondTaylor_of_C11 volume hS hF hFL
    have haG := ae_secondTaylor_of_C11 volume hS hG hGL
    have hP : ∀ᵐ z ∂volume,z∈S → z∈S ∧ DifferentiableAt ℝ (fderiv ℝ F) z ∧
        DifferentiableAt ℝ (fderiv ℝ G) z := by
      filter_upwards [haF,haG] with z hf hg hz
      exact ⟨hz,(hf hz).1,(hg hz).1⟩
    obtain ⟨z,hz,hact,hy,hp,hn,hf,hg,hsmall,hupp⟩ := simultaneous_C11_jensen_near volume
      hS hz0 hF hG hFL hGL hYL hPL hmax hN hP hrho heta
    have hdata := hactual z hact.1
    exact ⟨z,hact.1,hz,⟨hdata.1,hdata.2.1,hdata.2.2.1,hdata.2.2.2,
      hy,hp,hn,hact.2.1,hact.2.2,hf,hg⟩,hsmall,hupp⟩
  obtain ⟨z,H,K,hz,hzlim,hH,hK,hgrad,hquad⟩ :=
    exists_C11_hessian_limit_samples hS hFL hGL hselect
  exact ⟨⟨z,Y,H,K,hzlim,hH,hK,hgrad,hquad,S,hS,hz0,fun i=>(hz i).1,
    hF,hG,hFL.continuousOn,hGL.continuousOn,hYL.continuousOn,hactual,fun i=>(hz i).2⟩⟩
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_FamilyJensen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma WeakMTW.family_jensen_samples (hmtw : WeakMTW (n := n) (M := M))
    {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {Kp : Set P} (hKp : IsCompact Kp)
    (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s))) {Lφ : ℝ≥0}
    (hφL : ∀ p∈Kp,LipschitzWith Lφ (fun s=>Φ (p,s))) (A B : ℝ) (a : M) :
    ∃ R>0,∃ δ>0,∀ p∈Kp,∀ u:M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
      ∀ ψ:ℝ → ℝ,Continuous ψ → ∀ τ:ℝ,0<τ → τ<1/2 → τ<δ →
      ∀ c:M,extChartAt 𝓘(ℝ,Model n) a c∈ball (extChartAt 𝓘(ℝ,Model n) a a) R →
      let χ := extChartAt 𝓘(ℝ,Model n) a
      let w := fun y=>ψ (cTransform u y)
      let g := fun y=>Φ (p,cTransform u y)
      (∀ᶠ z in 𝓝 (χ c),chartOuterEnvelope w (1-τ) a z+chartCenterEnvelope g (1-τ) a z≤
        chartOuterEnvelope w (1-τ) a (χ c)+chartCenterEnvelope g (1-τ) a (χ c)) →
      ∀ N:Set (Model n),volume N=0 → Nonempty (JensenSamplesAt w g (1-τ) a c N) := by
  obtain ⟨R,hR,δ,hδ,H⟩ := hmtw.family_comparison_local_data hΦ hKp hmono hφL A B a
  refine ⟨R,hR,δ,hδ,?_⟩
  intro p hp u hu hb ψ hψ τ hτ hhalf hτδ c hc
  dsimp only
  intro hm N hN
  obtain ⟨r,hr,JF,JG,JY,JP,Y,hF,hG,hFL,hGL,hYL,hPL,hact⟩ :=
    H p hp u hu hb ψ hψ τ hτ hhalf hτδ c hc
  exact jensen_samples_at isOpen_ball (mem_ball_self hr) hF hG hFL hGL hYL hPL hact hm hN

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_MaximumJensenFamily
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumFamily.eventually_jensen_first_oai (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ} (ho : Continuous Bo)
    (hΦ : ContDiff ℝ ∞ (fun p:ℝ×ℝ=>p.2+p.1*Bc ((p.2-α)/D)))
    (hmono : ∀ b∈Icc bminus bplus,Monotone (fun s=>s+b*Bc ((s-α)/D))) {Lφ : ℝ≥0}
    (hLip : ∀ b∈Icc bminus bplus,LipschitzWith Lφ (fun s=>s+b*Bc ((s-α)/D)))
    {A B : ℝ} (hbound : ∀ y,v y∈Icc A B)
    (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo)
    {Q:TangentBundle 𝓘(ℝ,Model n) M}
    (hQ : Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 Q)) {N:Set (Model n)} (hN : volume N=0) :
    ∃ K:ℕ,Nonempty (MaximumJensenFamily hmtw hv ho (F.comp (fun k=>k+K) (tendsto_add_atTop_nat K))
      Q.1 (riemannianExp Q.1 Q.2) N) := by
  let c := riemannianExp Q.1 Q.2
  let χ := extChartAt 𝓘(ℝ,Model n) c
  obtain ⟨R,hR,δ,hδ,H⟩ := hmtw.family_jensen_samples hΦ isCompact_Icc hmono hLip A B c
  have hz := F.limit_coordinates hQ |>.2.2.1
  have hχ : Tendsto (fun k=>χ (F.z k)) atTop (𝓝 (χ c)) :=
    ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds
      (mem_extChartAt_source (I := 𝓘(ℝ,Model n)) c))).tendsto.comp hz
  have hpole := (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).tendsto Q |>.comp hQ
  have htime : Tendsto (fun k=>1-F.t k) atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_self] using (tendsto_const_nhds.sub F.time :
      Tendsto (fun k=>(1:ℝ)-F.t k) atTop (𝓝 (1-1)))
  have hevent : ∀ᶠ k in atTop,(F.row k).q.1.1∈(extChartAt 𝓘(ℝ,Model n) Q.1).source ∧
      F.z k∈χ.source ∧ χ (F.z k)∈ball (χ c) R ∧ 1-F.t k<1/2 ∧ 1-F.t k<δ := by
    filter_upwards [hpole.eventually ((isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source (I := 𝓘(ℝ,Model n)) Q.1)),
      hz.eventually ((isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source (I := 𝓘(ℝ,Model n)) c)),
      hχ.eventually (ball_mem_nhds _ hR),htime.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
      htime.eventually (gt_mem_nhds hδ)] with k ha hc hb ht hd
    exact ⟨ha,hc,hb,ht,hd⟩
  obtain ⟨K,hK⟩ := eventually_atTop.mp hevent
  let F1 := F.comp (fun k=>k+K) (tendsto_add_atTop_nat K)
  have hk (k:ℕ) := hK (k+K) (Nat.le_add_left _ _)
  have HJ : ∀ k,Nonempty (JensenSamplesAt (modifiedDatum v α D (F1.b k) Bo)
      (modifiedDatum v α D (F1.b k) Bc) (F1.t k) c (F1.z k) N) := by
    intro k
    have HB : ∀ y,cTransform u y∈Icc A B := by rwa [←hdual.2]
    have Hψ : Continuous (fun s:ℝ=>s+F1.b k*Bo ((s-α)/D)) :=
      continuous_id.add (continuous_const.mul (ho.comp ((continuous_id.sub continuous_const).div_const D)))
    have HH := H (F1.b k) (Ioo_subset_Icc_self (F1.parameter k)) u hu HB
      (fun s=>s+F1.b k*Bo ((s-α)/D)) Hψ (1-F1.t k) (by linarith [(F1.prefixTime k).2])
      (hk k).2.2.2.1 (hk k).2.2.2.2 (F1.z k) (hk k).2.2.1
    have hback : 1-(1-F1.t k)=F1.t k := by ring
    rw [hback,←hdual.2] at HH
    apply HH ?_ N hN
    have HM : ∀ w:Model n,
        chartOuterEnvelope (modifiedDatum v α D (F1.b k) Bo) (F1.t k) c w+
        chartCenterEnvelope (modifiedDatum v α D (F1.b k) Bc) (F1.t k) c w≤
        chartOuterEnvelope (modifiedDatum v α D (F1.b k) Bo) (F1.t k) c (χ (F1.z k))+
        chartCenterEnvelope (modifiedDatum v α D (F1.b k) Bc) (F1.t k) c (χ (F1.z k)) := by
      intro w
      have HX := F1.maximum k (F1.b k,χ.symm w) (Ioo_subset_Icc_self (F1.parameter k))
      dsimp only [regularizedComparison] at HX
      dsimp only [chartOuterEnvelope,chartCenterEnvelope]
      rw [show (extChartAt 𝓘(ℝ,Model n) c).symm (χ (F1.z k))=F1.z k from
        χ.left_inv (hk k).2.1]
      linarith only [HX]
    exact Eventually.of_forall HM
  let J := fun k=>Classical.choice (HJ k)
  let P := fun k=>Classical.choice ((F1.row k).jensen_first_limit hmtw hv ho
    (F1.prefixTime k).1 (F1.prefixTime k).2 (J k) (hk k).2.1 (hk k).1)
  exact ⟨K,⟨⟨fun k=>(hk k).1,fun k=>(hk k).2.1,J,P⟩⟩⟩

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.MaximumFamily.eventually_jensen_first_oai.{u_1} := @OAI.WeakMTWTransport.MaximumFamily.eventually_jensen_first_oai.{u_1}
