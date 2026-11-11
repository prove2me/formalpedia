-- Prove2me | solution 1 for OAI.WeakMTWTransport.chartJetMatrix_normal_identity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:43.669906+00:00
-- url     : https://prove2.me/submissions/24728126-7b23-4ca7-961e-68b4b1ac340e

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
import Definitions.Def_OAIQ232A026

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

lemma bilinear_isBigO_norm_mul {α : Type*} (L : Filter α)
    (B : E →L[ℝ] F →L[ℝ] G) (u : α → E) (v : α → F) :
    (fun x => B (u x) (v x)) =O[L] (fun x => ‖u x‖*‖v x‖) := by
  apply Asymptotics.IsBigO.of_bound ‖B‖
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      mul_assoc] using B.le_opNorm₂ (u x) (v x))

lemma bilinear_remainder_of_hasFDerivAt {a : E → F} {A : E →L[ℝ] F}
    (ha : HasFDerivAt a A 0) (ha0 : a 0=0) (B : F →L[ℝ] F →L[ℝ] ℝ) :
    (fun h => B (a h) (a h)-B (A h) (A h)) =o[𝓝 0] (fun h : E => ‖h‖^2) := by
  have hR : (fun h => a h-A h) =o[𝓝 0] (fun h : E => h) := by
    simpa only [zero_add,ha0,sub_zero] using hasFDerivAt_iff_isLittleO_nhds_zero.mp ha
  have hO : a =O[𝓝 0] (fun h : E => h) := by
    simpa only [ha0,sub_zero] using ha.isBigO_sub
  have hA : (fun h : E => A h) =O[𝓝 0] (fun h => h) := A.isBigO_id _
  have h1 := (bilinear_isBigO_norm_mul (𝓝 (0:E)) B (fun h => a h-A h) a).trans_isLittleO
    (hR.norm_left.norm_right.mul_isBigO hO.norm_left.norm_right)
  have h2 := (bilinear_isBigO_norm_mul (𝓝 (0:E)) B (fun h => A h) (fun h => a h-A h)).trans_isLittleO
    (hA.norm_left.norm_right.mul_isLittleO hR.norm_left.norm_right)
  have he : (fun h => B (a h) (a h)-B (A h) (A h)) =
      (fun h => B (a h-A h) (a h)+B (A h) (a h-A h)) := by
    funext h
    simp only [map_sub,_root_.sub_apply]
    ring
  rw [he]
  simpa only [pow_two] using h1.add h2

lemma HasSecondTaylor.comp_stationary {f : F → ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hf : HasSecondTaylor f 0 B)
    {a : E → F} {A : E →L[ℝ] F} (ha : HasFDerivAt a A 0) (ha0 : a 0=0) :
    HasSecondTaylor (fun h => f (a h)) 0
      (((ContinuousLinearMap.compL ℝ E F ℝ).flip A).comp (B.comp A)) := by
  have hO : (fun h : E => ‖a h‖) =O[𝓝 0] (fun h => ‖h‖) := by
    simpa only [ha0,sub_zero] using ha.isBigO_sub.norm_left.norm_right
  have ht : Tendsto a (𝓝 0) (𝓝 0) := ha0 ▸ ha.continuousAt
  have h1 := (hf.comp_tendsto ht).trans_isBigO (hO.pow 2)
  have h2 : (fun h => (B (a h) (a h)-B (A h) (A h))/2) =o[𝓝 0]
      (fun h : E => ‖h‖^2) := by
    simpa only [div_eq_mul_inv,mul_comm] using
      (bilinear_remainder_of_hasFDerivAt ha ha0 B).const_mul_left (2:ℝ)⁻¹
  unfold HasSecondTaylor
  have he : (fun h => f (a h)-f (a 0)-(0 : E →L[ℝ] ℝ) h-
      (((ContinuousLinearMap.compL ℝ E F ℝ).flip A).comp (B.comp A)) h h/2) =
      (fun h => (f (a h)-f 0-(0 : F →L[ℝ] ℝ) (a h)-B (a h) (a h)/2)+
        (B (a h) (a h)-B (A h) (A h))/2) := by
    funext h
    simp only [ha0,_root_.zero_apply,sub_zero,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply]
    ring
  rw [he]
  exact h1.add h2

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

lemma half_norm_sq_second_fderiv (p a d : E) :
    fderiv ℝ (fderiv ℝ (fun v : E => ‖v‖^2/2)) p a d=inner ℝ a d := by
  rw [half_norm_sq_fderiv]
  rw [(innerSL ℝ).hasFDerivAt.fderiv]
  rfl

lemma half_norm_sq_contDiff : ContDiff ℝ ∞ (fun v : E => ‖v‖^2/2) := by
  simpa only [one_div,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm,one_mul] using
    ((contDiff_norm_sq (𝕜 := ℝ) (E := E) (n := ∞)).const_smul (1/2:ℝ))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_JetTranslation
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
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma fderiv_translate_at_zero {f:E → F} {x:E} (hf:DifferentiableAt ℝ f x) (c:F) :
    fderiv ℝ (fun h=>f (x+h)-c) 0=fderiv ℝ f x := by
  rw [fderiv_sub_const]
  have H:=(show HasFDerivAt f (fderiv ℝ f x) (x+id 0) from by simpa only [id_eq,add_zero] using hf.hasFDerivAt).comp 0 ((hasFDerivAt_id (0:E)).const_add x)
  simpa only [Function.comp_def,add_zero,ContinuousLinearMap.comp_id] using H.fderiv

lemma second_fderiv_translate_at_zero {f:E → F} {x:E} (hf:ContDiffAt ℝ 2 f x) (c:F) :
    fderiv ℝ (fderiv ℝ (fun h=>f (x+h)-c)) 0=fderiv ℝ (fderiv ℝ f) x := by
  have ht:Tendsto (fun h:E=>x+h) (𝓝 0) (𝓝 x):=by
    have hc : ContinuousAt (fun h:E=>x+h) 0 := continuousAt_const.add continuousAt_id
    have H:=hc.tendsto
    rw [add_zero] at H
    exact H
  have hd:∀ᶠ y in 𝓝 x,DifferentiableAt ℝ f y:=
    (hf.eventually (by norm_num)).mono (fun _ h=>h.differentiableAt (by norm_num))
  have he:fderiv ℝ (fun h=>f (x+h)-c)=ᶠ[𝓝 (0:E)] (fun h=>fderiv ℝ f (x+h)):=by
    filter_upwards [ht.eventually hd] with h hh
    rw [fderiv_sub_const]
    have H:=hh.hasFDerivAt.comp h ((hasFDerivAt_id h).const_add x)
    simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using H.fderiv
  rw [he.fderiv_eq]
  have hfd:DifferentiableAt ℝ (fderiv ℝ f) x:=
    (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have H:=(show HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (x+id 0) from by simpa only [id_eq,add_zero] using hfd.hasFDerivAt).comp 0 ((hasFDerivAt_id (0:E)).const_add x)
  simpa only [Function.comp_def,add_zero,ContinuousLinearMap.comp_id] using H.fderiv
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ScalarExpansion
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

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarJetFormula
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
omit [CompleteSpace E] in
lemma quadraticTaylor_hasFDerivAt (f0:ℝ) (p:E) {A:E →L[ℝ] E}
    (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e)) (x:E) :
    HasFDerivAt (quadraticTaylor f0 p A) (innerSL ℝ (p+A x)) x := by
  have H:=((hasFDerivAt_const f0 x).add ((innerSL ℝ p).hasFDerivAt)).add
    ((A.hasFDerivAt.inner ℝ (hasFDerivAt_id x)).const_smul (1/2:ℝ))
  convert! H using 1
  · funext d
    simp only [quadraticTaylor, Pi.add_apply, Pi.smul_apply, innerSL_apply_apply, smul_eq_mul, id_eq]
    ring
  · ext d
    simp only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
      fderivInnerCLM_apply,inner_add_left,zero_add,smul_eq_mul, id_eq]
    rw [hA d x,real_inner_comm d (A x)]
    ring

omit [CompleteSpace E] in
lemma quadraticTaylor_second_fderiv (f0:ℝ) (p:E) {A:E →L[ℝ] E}
    (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e)) (x:E) :
    fderiv ℝ (fderiv ℝ (quadraticTaylor f0 p A)) x=(innerSL ℝ).comp A := by
  have he:fderiv ℝ (quadraticTaylor f0 p A)=(fun x=>innerSL ℝ (p+A x)):= by
    funext x
    exact (quadraticTaylor_hasFDerivAt f0 p hA x).fderiv
  rw [he]
  have H:=((innerSL ℝ).hasFDerivAt).comp x ((hasFDerivAt_const p x).add A.hasFDerivAt)
  simpa only [zero_add,Function.comp_def,Pi.add_apply] using H.fderiv

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_TaylorPositivity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma HasSecondTaylor.nonneg_of_localMin {f : E → ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f 0 B)
    (hm : IsLocalMin f 0) (v:E) : 0≤B v v := by
  by_contra hn
  have hB : B v v<0 := lt_of_not_ge hn
  have hv : v≠0 := by
    intro he; subst v; simp at hB
  have hnv : 0<‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  let ε := -(B v v)/(4*‖v‖^2)
  have hε : 0<ε := div_pos (neg_pos.mpr hB) (by positivity)
  have hεeq : ε*‖v‖^2 = -(B v v)/4 := by
    dsimp [ε]; field_simp
  obtain ⟨r,hr,H⟩ := Metric.eventually_nhds_iff.mp ((hf.eventually hε).and hm)
  let δ := r/(2*(‖v‖+1))
  have hδ : 0<δ := div_pos hr (by positivity)
  have hδeq : δ*(2*(‖v‖+1))=r := div_mul_cancel₀ _ (by positivity)
  have hmem : δ • v∈Metric.ball (0:E) r := by
    rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hδ]
    nlinarith [norm_nonneg v]
  obtain ⟨ht,hm'⟩ := H hmem
  have hbil : B (δ • v) (δ • v)=δ^2*B v v := by
    simp only [map_smul,smul_apply,smul_eq_mul] <;> ring
  have hnorm : ‖δ • v‖^2=δ^2*‖v‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hδ,mul_pow]
  rw [hbil,hnorm] at ht
  simp only [zero_apply,sub_zero] at ht
  have hupper := (abs_le.mp ht).2
  have hmul : ε*(δ^2*‖v‖^2)=δ^2*(-(B v v)/4) := by
    calc
      _=δ^2*(ε*‖v‖^2) := by ring
      _=_ := by rw [hεeq]
  rw [hmul] at hupper
  have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos hδ) hB
  change f 0≤f (δ • v) at hm'
  nlinarith
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

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SecondTaylorComposition
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
variable {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma HasSecondTaylor.diagonal_unique {f:E → ℝ} {l:E →L[ℝ] ℝ}
    {B C:E →L[ℝ] E →L[ℝ] ℝ} (hB:HasSecondTaylor f l B) (hC:HasSecondTaylor f l C) (d:E) :
    B d d=C d d := by
  have h1:HasSecondTaylor (fun h=>f h-f h) 0 (B-C):=by simpa only [sub_self] using hB.sub hC
  have h2:HasSecondTaylor (fun h=>f h-f h) 0 (C-B):=by simpa only [sub_self] using hC.sub hB
  have hm:IsLocalMin (fun h=>f h-f h) 0:=by
    exact Eventually.of_forall (fun h=>by simp)
  have H1:=h1.nonneg_of_localMin hm d
  have H2:=h2.nonneg_of_localMin hm d
  simp only [sub_apply] at H1 H2
  linarith

lemma HasSecondTaylor.congr_of_eventuallyEq {f g:E → ℝ} {l:E →L[ℝ] ℝ}
    {B:E →L[ℝ] E →L[ℝ] ℝ} (hf:HasSecondTaylor f l B) (he:g=ᶠ[𝓝 0] f) :
    HasSecondTaylor g l B := by
  have h0:=he.self_of_nhds
  apply hf.congr' _ (Eventually.of_forall (fun _=>rfl))
  filter_upwards [he] with h hh
  rw [hh,h0]

lemma HasQuadraticExpansion.hasSecondTaylor' {f:E → ℝ} {p:E} {A:E →L[ℝ] E}
    (hf:HasQuadraticExpansion f p A) :
    HasSecondTaylor f (innerSL ℝ p) ((innerSL ℝ).comp A) := by
  have H:=quadratic_expansion_polynomial_remainder hf
  unfold HasSecondTaylor
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext h
  simp only [quadraticTaylor,ContinuousLinearMap.comp_apply,innerSL_apply_apply]
  ring

lemma quadratic_expansion_comp_proxy {f:F → ℝ} {p:F} {A:F →L[ℝ] F}
    (hf:HasQuadraticExpansion f p A) {g:E → F} (hg:ContDiffAt ℝ 2 g 0) (hg0:g 0=0) :
    let P:=quadraticTaylor (f 0) p A
    HasSecondTaylor (fun h=>f (g h)) (fderiv ℝ (fun h=>P (g h)) 0)
      (fderiv ℝ (fderiv ℝ (fun h=>P (g h))) 0) := by
  let P:=quadraticTaylor (f 0) p A
  have hP:ContDiff ℝ 2 P:=by
    dsimp only [P,quadraticTaylor]
    exact (contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).add
      ((A.contDiff.inner ℝ contDiff_id).div_const 2)
  have hQ:ContDiffAt ℝ 2 (fun h=>P (g h)) 0:=hP.contDiffAt.comp 0 hg
  apply (hasSecondTaylor_of_contDiffAt hQ).of_littleO_difference
  · simp only [hg0,P,quadraticTaylor,map_zero,inner_zero_right,zero_div,add_zero]
  · have hgd:HasFDerivAt g (fderiv ℝ g 0) 0:=(hg.differentiableAt (by norm_num)).hasFDerivAt
    have ht:Tendsto g (𝓝 0) (𝓝 0):=hg0 ▸ hg.continuousAt.tendsto
    have hO:(fun h:E=>‖g h‖)=O[𝓝 0] (fun h=>‖h‖):=by
      simpa only [hg0,sub_zero] using hgd.isBigO_sub.norm_left.norm_right
    exact ((quadratic_expansion_polynomial_remainder hf).comp_tendsto ht).trans_isBigO (hO.pow 2)

lemma quadratic_proxy_pullback {f0:ℝ} {p:F} {A:F →L[ℝ] F}
    (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e))
    {g:E → F} (hg:ContDiffAt ℝ 2 g 0) (hg0:g 0=0) :
    fderiv ℝ (fderiv ℝ (fun h=>quadraticTaylor f0 p A (g h))) 0=
      secondJetPullback (innerSL ℝ p) ((innerSL ℝ).comp A)
        (fderiv ℝ g 0) (fderiv ℝ (fderiv ℝ g) 0) := by
  have hP:ContDiff ℝ 2 (quadraticTaylor f0 p A):=by
    change ContDiff ℝ 2 (fun h:F=>f0+inner ℝ p h+inner ℝ (A h) h/2)
    exact (contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).add
      ((A.contDiff.inner ℝ contDiff_id).div_const 2)
  ext d e
  rw [second_fderiv_comp_at (Eventually.of_forall (fun _=>hP.differentiable (by norm_num) _))
    (((hP.contDiffAt.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num))) hg]
  rw [hg0,quadraticTaylor_second_fderiv f0 p hA]
  rw [show fderiv ℝ (quadraticTaylor f0 p A) 0=innerSL ℝ p from by
    simpa only [map_zero,add_zero] using (quadraticTaylor_hasFDerivAt f0 p hA 0).fderiv]
  rfl
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalPoleTaylor
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
section TaylorUniqueness
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in
lemma HasSecondTaylor.hasFDerivAt' {f:E → ℝ} {l:E →L[ℝ] ℝ} {H:E →L[ℝ] E →L[ℝ] ℝ}
    (hf:HasSecondTaylor f l H) : HasFDerivAt f l 0 := by
  have hNorm : (fun offset : E => ‖offset‖) =o[𝓝 0] (fun _ => (1:ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr (by
      simpa only [norm_zero] using continuous_norm.tendsto (0:E))
  have hSquare : (fun offset : E => ‖offset‖^2) =o[𝓝 0]
      (fun offset : E => ‖offset‖) := by
    simpa only [pow_two,one_mul] using
      hNorm.mul_isBigO (Asymptotics.isBigO_refl (fun offset : E => ‖offset‖) (𝓝 0))
  have hBilinear : (fun offset : E => H offset offset) =o[𝓝 0]
      (fun offset : E => ‖offset‖) :=
    (bilinear_isBigO_norm_mul (𝓝 (0:E)) H (fun offset => offset)
      (fun offset => offset)).trans_isLittleO
      (by simpa only [pow_two] using hSquare)
  have hQuadratic : (fun offset : E => H offset offset/2) =o[𝓝 0]
      (fun offset : E => ‖offset‖) := by
    simpa only [div_eq_mul_inv,mul_comm] using hBilinear.const_mul_left (2:ℝ)⁻¹
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa only [zero_add,sub_add_cancel] using
    ((hf.trans_isBigO hSquare.isBigO).add hQuadratic).of_norm_right

omit [FiniteDimensional ℝ E] in
lemma HasSecondTaylor.diagonal_unique' {f:E → ℝ} {l k:E →L[ℝ] ℝ}
    {H K:E →L[ℝ] E →L[ℝ] ℝ} (hf:HasSecondTaylor f l H) (hg:HasSecondTaylor f k K) (d:E) :
    H d d=K d d := by
  have he:=hf.hasFDerivAt'.unique hg.hasFDerivAt'
  subst k
  exact hf.diagonal_unique hg d
end TaylorUniqueness
section NormalPoleTaylor
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFinitePole_rc05b7c_1 (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance tangentCompletePole_rc05b7c_1 (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _
omit [Nonempty M] in
lemma normal_stationary_pole_taylor {f:M → ℝ} {x y:M}
    {r:TangentSpace 𝓘(ℝ,Model n) y} {q:TangentSpace 𝓘(ℝ,Model n) x}
    (hr:r∈injectivityDomain y) (hq:q∈injectivityDomain x)
    (hyx:riemannianExp y r=x)
    {S:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hS:HasQuadraticExpansion (fun h=>f (riemannianExp y h)) r S)
    {R:TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hR:DifferentiableAt ℝ R q) (hR0:R q=0)
    (hRe:∀ᶠ v in 𝓝 q,riemannianExp y (R v)=riemannianExp x v) :
    HasSecondTaylor (fun h=>f (riemannianExp x (q+h))+‖q+h‖^2/2) 0
      (pullBilinear (((innerSL ℝ).comp S : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ)+normalHessian y r) (fderiv ℝ R q)) := by
  let C:=normalCost y r
  have hc:ContDiffAt ℝ 2 C 0:=
    (normalCost_contDiffAt hr).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hct:HasSecondTaylor C (innerSL ℝ (-r)) (normalHessian y r):=by
    simpa only [C,(normalCost_hasFDerivAt_zero hr).fderiv,normalHessian] using
      hasSecondTaylor_of_contDiffAt hc
  have H:HasSecondTaylor (fun h=>f (riemannianExp y h)+C h) 0
      (((innerSL ℝ).comp S : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ)+normalHessian y r):=by
    simpa only [map_neg,add_neg_cancel] using hS.hasSecondTaylor'.add hct
  have ha:HasFDerivAt (fun h=>R (q+h)) (fderiv ℝ R q) 0:=by
    simpa only [Function.comp_def,add_zero,ContinuousLinearMap.comp_id] using
      (show HasFDerivAt R (fderiv ℝ R q) (q+0) from by simpa only [add_zero] using hR.hasFDerivAt).comp 0 ((hasFDerivAt_id (0:TangentSpace 𝓘(ℝ,Model n) x)).const_add q)
  have hs:=H.comp_stationary ha (by simpa only [add_zero] using hR0)
  apply hs.congr_of_eventuallyEq
  have ht:Tendsto (fun h:TangentSpace 𝓘(ℝ,Model n) x=>q+h) (𝓝 0) (𝓝 q):=by
    have hc : ContinuousAt (fun h:TangentSpace 𝓘(ℝ,Model n) x=>q+h) 0 := continuousAt_const.add continuousAt_id
    simpa only [add_zero] using hc.tendsto
  filter_upwards [ht.eventually hRe,ht.eventually ((isOpen_injectivityDomain x).mem_nhds hq)] with h hh hhr
  dsimp only [C,normalCost]
  rw [hh,hyx]
  congr 1
  change ‖q+h‖^2/2=dist (riemannianExp x (q+h)) x^2/2
  rw [dist_comm,injectivityDomain_subset_minimizingVectors x hhr]
end NormalPoleTaylor
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalFrameTaylor
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
section NormalFrameTaylor
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteNF_rc05b7c_1 (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance tangentCompleteNF_rc05b7c_1 (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _
omit [Nonempty M] in
lemma chart_normal_pole_frame_identity {E:Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] {f:M → ℝ} {x y a:M}
    {r:TangentSpace 𝓘(ℝ,Model n) y} {q:TangentSpace 𝓘(ℝ,Model n) x}
    (B:E →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x)
    (hr:r∈injectivityDomain y) (hq:q∈injectivityDomain x)
    (hyx:riemannianExp y r=x) (hxy:riemannianExp x q=y)
    (hy:y∈(extChartAt 𝓘(ℝ,Model n) a).source)
    {S:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hS:HasQuadraticExpansion (fun h=>f (riemannianExp y h)) r S)
    {p:Model n} {A:Model n →L[ℝ] Model n}
    (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e))
    (hAe:HasQuadraticExpansion (fun h=>f ((extChartAt 𝓘(ℝ,Model n) a).symm
      (extChartAt 𝓘(ℝ,Model n) a y+h))) p A)
    {R:TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hR:DifferentiableAt ℝ R q) (hR0:R q=0)
    (hRe:∀ᶠ v in 𝓝 q,riemannianExp y (R v)=riemannianExp x v) :
    let g:=fun h:E=>
      extChartAt 𝓘(ℝ,Model n) a (riemannianExp x (q+B h))-extChartAt 𝓘(ℝ,Model n) a y
    ∀d,‖B d‖^2+secondJetPullback (innerSL ℝ p) ((innerSL ℝ).comp A)
      (fderiv ℝ g 0) (fderiv ℝ (fderiv ℝ g) 0) d d=
      inner ℝ (S (fderiv ℝ R q (B d))) (fderiv ℝ R q (B d))+
        normalHessian y r (fderiv ℝ R q (B d)) (fderiv ℝ R q (B d)) := by
  dsimp only
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  let g:=fun h:E=>χ (riemannianExp x (q+B h))-χ y
  have hg0:g 0=0:=by simp only [g,map_zero,add_zero,hxy,sub_self]
  have hchart:ContDiffAt ℝ ∞ (fun v:TangentSpace 𝓘(ℝ,Model n) x=>χ (riemannianExp x v)) q:=by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (contMDiffAt_extChartAt' (x:=a) (by simpa only [hxy,extChartAt_source] using hy)).comp q
      (contMDiff_riemannianExp_fiber x q)
  have hg:ContDiffAt ℝ 2 g 0:=by
    apply ContDiffAt.of_le _ (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hc : ContDiffAt ℝ ∞ (fun v:TangentSpace 𝓘(ℝ,Model n) x=>χ (riemannianExp x v)) (q+B 0) := by
      simpa only [map_zero,add_zero] using hchart
    exact (hc.comp 0 (contDiffAt_const.add B.contDiff.contDiffAt)).sub contDiffAt_const
  have H:=quadratic_expansion_comp_proxy hAe hg hg0
  simp only [add_zero] at H
  let P:=quadraticTaylor (f (χ.symm (χ y))) p A
  have he:HasSecondTaylor (fun h=>f (riemannianExp x (q+B h)))
      (fderiv ℝ (fun h=>P (g h)) 0) (fderiv ℝ (fderiv ℝ (fun h=>P (g h))) 0):=by
    apply H.congr_of_eventuallyEq
    have ht:ContinuousAt (fun h:E=>riemannianExp x (q+B h)) 0:=
      (contMDiff_riemannianExp_fiber x).continuous.continuousAt.comp (continuousAt_const.add B.continuous.continuousAt)
    have hh:=ht.eventually ((isOpen_extChartAt_source a).mem_nhds (by simpa only [map_zero,add_zero,hxy] using hy))
    filter_upwards [hh] with h hh
    change f (riemannianExp x (q+B h))=f (χ.symm (χ y+(χ (riemannianExp x (q+B h))-χ y)))
    rw [show χ y+(χ (riemannianExp x (q+B h))-χ y)=χ (riemannianExp x (q+B h)) by abel,χ.left_inv hh]
  have hn:ContDiffAt ℝ 2 (fun h:E=>‖q+B h‖^2/2) 0:=
    (half_norm_sq_contDiff.comp (contDiff_const.add B.contDiff)).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HT:=he.add (hasSecondTaylor_of_contDiffAt hn)
  have HT2:=(normal_stationary_pole_taylor hr hq hyx hS hR hR0 hRe).comp_stationary B.hasFDerivAt (map_zero B)
  intro d
  have HH:=HT.diagonal_unique' HT2 d
  rw [quadratic_proxy_pullback hA hg hg0] at HH
  simp only [add_apply,ContinuousLinearMap.comp_apply] at HH
  have hshift: fderiv ℝ (fderiv ℝ (fun h:E=>‖q+B h‖^2/2)) 0 d d=‖B d‖^2:=by
    have hf:ContDiffAt ℝ 2 (fun v:TangentSpace 𝓘(ℝ,Model n) x=>‖v‖^2/2) (q+B 0) :=
      half_norm_sq_contDiff.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    simpa only [ContinuousLinearMap.id_apply,half_norm_sq_second_fderiv,innerSL_apply_apply,real_inner_self_eq_norm_sq] using
      second_fderiv_comp_affine B q 0 hf d d
  rw [hshift] at HH
  change secondJetPullback (innerSL ℝ p) ((innerSL ℝ).comp A)
    (fderiv ℝ g 0) (fderiv ℝ (fderiv ℝ g) 0) d d+‖B d‖^2=
    inner ℝ (S (fderiv ℝ R q (B d))) (fderiv ℝ R q (B d))+
    normalHessian y r (fderiv ℝ R q (B d)) (fderiv ℝ R q (B d)) at HH
  linarith only [HH]
end NormalFrameTaylor
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_StationaryPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma second_fderiv_const_mul {f : E → ℝ} {x : E} (c : ℝ) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => c*f a)) x v w = c*fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fderiv ℝ (c • f)) x v w = _
  rw [fderiv_const_smul_field c]
  rw [fderiv_const_smul_field (f := fderiv ℝ f) c]
  rfl

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_PrefixAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

lemma prefixAction_axis {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x) :
    prefixAction x t (0,p)=t*(‖p‖^2/2) := by
  have hm := injectivityDomain_subset_minimizingVectors x hp
  change dist x (riemannianExp x (t • p))=‖t • p‖ at hm
  simp only [prefixAction,riemannianExp_zero,cost,hm,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs]
  by_cases ht : t=0
  · simp [ht]
  · field_simp

lemma prefixAction_axis_near {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x) :
    (fun v => prefixAction x t (0,v)) =ᶠ[𝓝 p] (fun v => t*(‖v‖^2/2)) := by
  have hn : ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 p, t • v ∈ injectivityDomain x :=
    (continuous_const_smul t).continuousAt.eventually ((isOpen_injectivityDomain x).mem_nhds hp)
  filter_upwards [hn] with v hv
  exact prefixAction_axis hv

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MovingPrefix
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

lemma movingPrefix_contMDiffAt {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (Function.uncurry (movingPrefix a t)) (b,p) := by
  exact (movingNormal_contMDiffAt (q := (b,t • p)) hb).comp (b,p)
    (contDiffAt_fst.prodMk (contDiffAt_snd.const_smul t)).contMDiffAt

lemma movingPrefixChart_contDiffAt {a c : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingPrefixChart a c t)) (b,p) := by
  exact ((contMDiffAt_extChartAt' (I := 𝓘(ℝ,Model n)) (by simpa only [extChartAt_source,Function.uncurry] using hc)) |>.comp (b,p)
      (movingPrefix_contMDiffAt hb)).contDiffAt

lemma movingPrefixEnergy_axis_near {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    (movingPrefixEnergy a t b)=ᶠ[𝓝 p]
      (fun q=>t*(‖(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) q‖^2/2)) := by
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
    ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  filter_upwards [(L.continuous.tendsto p).eventually (prefixAction_axis_near hp)] with q hq
  simpa only [movingPrefixEnergy,movingNormal_zero hb,movingPrefix_eq hb,
    prefixAction,riemannianExp_zero] using hq

lemma movingPrefixEnergy_hessian {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) (d e : Model n) :
    fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p d e=
      t*inner ℝ
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) d)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) e) := by
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
    ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  rw [((movingPrefixEnergy_axis_near hb hp).fderiv (𝕜 := ℝ)).fderiv_eq]
  rw [second_fderiv_const_mul]
  have H := second_fderiv_comp_affine (f := fun q=>‖q‖^2/2) L 0 p
    ((half_norm_sq_contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt) d e
  simpa only [zero_add,half_norm_sq_second_fderiv,innerSL_apply_apply,smul_apply,
    smul_eq_mul] using congrArg (fun r:ℝ=>t*r) H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FrameMetric
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
section FrameMetric
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma frameMetric_apply {a:M} {b:Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (d e:Model n) :
    frameMetric a b d e=inner ℝ (chartFiberInverse a b d) (chartFiberInverse a b e) := by
  have hp : (1:ℝ) • chartFiberInverse a b 0∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) := by
    simpa only [map_zero,smul_zero] using zero_mem_injectivityDomain
      (n := n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  simpa only [frameMetric,chartFiberInverse,one_mul] using movingPrefixEnergy_hessian hb hp d e

end FrameMetric
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ChartTrueMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
section ChartTrueMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma chartJetMatrix_normal_identity_oai {f:M → ℝ} {a c y:M} {b q:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hq:chartFiberInverse a b q∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hy:movingPrefix a 1 b q=y) (hc:y∈(extChartAt 𝓘(ℝ,Model n) c).source)
    {r:TangentSpace 𝓘(ℝ,Model n) y} (hr:r∈injectivityDomain y)
    (hrx:riemannianExp y r=(extChartAt 𝓘(ℝ,Model n) a).symm b)
    {S:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hS:HasQuadraticExpansion (fun h=>f (riemannianExp y h)) r S)
    {p:Model n} {A:Model n →L[ℝ] Model n} (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e))
    (hAe:HasQuadraticExpansion (fun h=>f ((extChartAt 𝓘(ℝ,Model n) c).symm
      (extChartAt 𝓘(ℝ,Model n) c y+h))) p A)
    {R:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b) → TangentSpace 𝓘(ℝ,Model n) y}
    (hR:DifferentiableAt ℝ R (chartFiberInverse a b q)) (hR0:R (chartFiberInverse a b q)=0)
    (hRe:∀ᶠ v in 𝓝 (chartFiberInverse a b q),riemannianExp y (R v)=
      riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) v) :
    ∀d,chartJetMatrix a c b q (innerSL ℝ p) ((innerSL ℝ).comp A) d d=
      inner ℝ (S (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d)))
        (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))+
      normalHessian y r (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))
        (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d)) := by
  let B:=chartFiberInverse a b
  have he:riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) (B q)=y:=by
    simpa only [movingPrefix_eq hb,one_smul,B,chartFiberInverse] using hy
  have H:=chart_normal_pole_frame_identity B hr hq hrx he hc hS hA hAe hR hR0 hRe
  have hg:ContDiffAt ℝ 2 (movingPrefixChart a c 1 b) q:=by
    exact ((movingPrefixChart_contDiffAt hb (hy.symm ▸ hc)).comp q
      (contDiffAt_const.prodMk contDiffAt_id)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have heq:(fun h=>movingPrefixChart a c 1 b (q+h)-extChartAt 𝓘(ℝ,Model n) c y)=
      (fun h=>extChartAt 𝓘(ℝ,Model n) c (riemannianExp
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) (B q+B h))-extChartAt 𝓘(ℝ,Model n) c y):=by
    funext h
    simp only [movingPrefixChart,movingPrefix_eq hb,one_smul,map_add,B,chartFiberInverse]
  rw [←heq] at H
  dsimp only at H
  rw [fderiv_translate_at_zero (hg.differentiableAt (by norm_num)),
    second_fderiv_translate_at_zero hg] at H
  intro d
  rw [chartJetMatrix,add_apply,add_apply,
    frameMetric_apply hb,real_inner_self_eq_norm_sq]
  exact H d

end ChartTrueMatrix
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.chartJetMatrix_normal_identity_oai.{u_1} := @OAI.WeakMTWTransport.chartJetMatrix_normal_identity_oai.{u_1}
