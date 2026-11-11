-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.actualPole_residual_taylor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T18:52:28.094069+00:00
-- url     : https://prove2.me/submissions/e2c38cf3-341f-485b-8594-ad03a437bcf0

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
import Definitions.Def_OAIQ232A013
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_actualPole_taylor

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_JetPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_comp_affine {f : F → ℝ} (L : E →L[ℝ] F) (b : F) (x : E)
    (hf : ContDiffAt ℝ 2 f (b+L x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun h => f (b+L h))) x v w =
      fderiv ℝ (fderiv ℝ f) (b+L x) (L v) (L w) := by
  have hL : ∀ y:E, HasFDerivAt (fun h : E => b+L h) L y :=
    fun y => (L.hasFDerivAt (x := y)).const_add b
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := fun h : E => b+L h) x (hL x)
  have H := hd.clm_comp (hasFDerivAt_const L x)
  have heq : (fun h => fderiv ℝ f (b+L h) |>.comp L) =ᶠ[𝓝 x]
      (fderiv ℝ (fun h => f (b+L h))) := by
    have hn := (hL x).continuousAt.eventually (hf.eventually (by norm_num))
    filter_upwards [hn] with h hh
    exact ((hh.differentiableAt (by norm_num)).hasFDerivAt.comp
      (f := fun h : E => b+L h) h (hL h)).fderiv.symm
  have he := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v w)
    (H.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,map_zero,ContinuousLinearMap.comp_zero,
    zero_add,add_apply,zero_apply] using he

lemma hasSecondTaylor_shift {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    HasSecondTaylor (fun h => f (x+h)) (fderiv ℝ f x)
      (fderiv ℝ (fderiv ℝ f) x) := by
  have hc : ContDiffAt ℝ 2 (fun h => f (x+h)) 0 := by
    exact (show ContDiffAt ℝ 2 f (x+(0:E)) by simpa using hf).comp 0
      (contDiffAt_const.add contDiffAt_id)
  have H := hasSecondTaylor_of_contDiffAt hc
  have hD : fderiv ℝ (fun h => f (x+h)) 0=fderiv ℝ f x := by
    have hd := (hf.differentiableAt (by norm_num)).hasFDerivAt
    have hl := (hasFDerivAt_id (𝕜 := ℝ) (0:E)).const_add x
    simpa only [add_zero,ContinuousLinearMap.comp_id,Function.comp_def] using
      ((show HasFDerivAt f (fderiv ℝ f x) (x+(0:E)) by simpa using hd).comp
        (f := fun h : E => x+h) 0 hl).fderiv
  have hDD : fderiv ℝ (fderiv ℝ (fun h => f (x+h))) 0=
      fderiv ℝ (fderiv ℝ f) x := by
    ext v w
    simpa only [ContinuousLinearMap.id_apply,add_zero] using
      second_fderiv_comp_affine (ContinuousLinearMap.id ℝ E) x 0
        (by simpa using hf) v w
  rwa [hD,hDD] at H

end

open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma half_norm_sq_hasFDerivAt (p : E) :
    HasFDerivAt (fun v : E => ‖v‖^2/2) (innerSL ℝ p) p := by
  have H := ((hasFDerivAt_id (𝕜 := ℝ) p).norm_sq).const_smul (1/2:ℝ)
  convert! H using 1
  · ext v; simp only [Pi.smul_apply,smul_eq_mul,id_eq] <;> ring
  · ext a
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
      smul_apply,smul_eq_mul,innerSL_apply_apply,id_eq]
    ring

lemma half_norm_sq_fderiv :
    fderiv ℝ (fun v : E => ‖v‖^2/2) = innerSL ℝ := by
  funext p
  exact (half_norm_sq_hasFDerivAt p).fderiv

lemma half_norm_sq_contDiff : ContDiff ℝ ∞ (fun v : E => ‖v‖^2/2) := by
  simpa only [one_div,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm,one_mul] using
    ((contDiff_norm_sq (𝕜 := ℝ) (E := E) (n := ∞)).const_smul (1/2:ℝ))

lemma norm_square_hasSecondTaylor (p : E) :
    HasSecondTaylor (fun h : E => ‖p+h‖^2/2) (innerSL ℝ p) (innerSL ℝ) := by
  have hc : ContDiffAt ℝ 2 (fun v : E => ‖v‖^2/2) p :=
    ((half_norm_sq_contDiff (E := E)).of_le
      (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have H := hasSecondTaylor_shift hc
  simpa only [half_norm_sq_fderiv,(innerSL ℝ).hasFDerivAt.fderiv] using H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_PoleJetAlgebra
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma HasSecondTaylor.const_mul {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) (c:ℝ) :
    HasSecondTaylor (fun h => c*f h) (c • l) (c • B) := by
  unfold HasSecondTaylor at *
  have he : (fun h => c*f h-c*f 0-(c • l) h-(c • B) h h/2) =
      (fun h => c*(f h-f 0-l h-B h h/2)) := by
    funext h; simp only [smul_apply,smul_eq_mul] <;> ring
  rw [he]
  exact hf.const_mul_left c

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_ActualLowerJet
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

lemma WeakMTW.actualPole_residual_taylor_oai (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (harep : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    HasSecondTaylor (fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • (p+d)))-t*(‖p+d‖^2/2))
      0 (-((innerSL ℝ).comp R)) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have H := (hmtw.actualPole_taylor hu hv hdual ht ht1 hp ha ha0 harep).1.sub
    ((norm_square_hasSecondTaylor p).const_mul t)
  have hlin : t • innerSL ℝ p-t • innerSL ℝ p=(0:V →L[ℝ] ℝ) := sub_self _
  have hbil : (t • (innerSL ℝ (E := V))-(innerSL ℝ).comp R)-t • innerSL ℝ =
      -((innerSL ℝ).comp R) := by
    apply ContinuousLinearMap.ext; intro d
    apply ContinuousLinearMap.ext; intro e
    change (t*inner ℝ d e-inner ℝ (R d) e)-t*inner ℝ d e = -inner ℝ (R d) e
    ring
  rw [hlin,hbil] at H
  exact H

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.actualPole_residual_taylor_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.actualPole_residual_taylor_oai.{u_1}
