-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_true_center_jet_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:52.715277+00:00
-- url     : https://prove2.me/submissions/a94cdfd1-bfc9-4b9c-b36b-7b52fdc1fd91

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
import Definitions.Def_OAIQ232A025
import Definitions.Def_OAIQ232A026
import Theorems.Thm_OAI_WeakMTWTransport_chartJetMatrix_normal_identity
import Theorems.Thm_OAI_WeakMTWTransport_exists_uniform_true_center_gain

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SecondFderivScalarComp
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma second_fderiv_scalar_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {φ : ℝ → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (ξ : E) :
    fderiv ℝ (fderiv ℝ (fun h => φ (f h))) x ξ ξ =
      iteratedDeriv 2 φ (f x)*(fderiv ℝ f x ξ)^2+
        deriv φ (f x)*fderiv ℝ (fderiv ℝ f) x ξ ξ := by
  let g := fun t : ℝ => f (x+t • ξ)
  have hg : ContDiffAt ℝ 2 g 0 := by
    change ContDiffAt ℝ 2 (f ∘ fun t : ℝ => x+t • ξ) 0
    exact (show ContDiffAt ℝ 2 f (x+(0:ℝ) • ξ) from by simpa using hf).comp (0:ℝ)
      (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hg0 : g 0=f x := by simp [g]
  have hline : HasDerivAt (fun t : ℝ => x+t • ξ) ξ 0 := by
    convert! (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const ξ) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hd : deriv g 0=fderiv ℝ f x ξ := by
    simpa only [Function.comp_def,g,zero_smul,add_zero] using
      ((show HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ) • ξ) from by
        simpa only [zero_smul,add_zero] using (hf.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt (0:ℝ) hline).deriv
  have H := iteratedDeriv_comp_two (show ContDiffAt ℝ 2 φ (g 0) from hg0.symm ▸ hφ) hg
  rw [hg0,hd,show iteratedDeriv 2 g 0=fderiv ℝ (fderiv ℝ f) x ξ ξ from
    iteratedDeriv_two_affine_line hf ξ] at H
  change fderiv ℝ (fderiv ℝ (φ ∘ f)) x ξ ξ = _
  rw [←iteratedDeriv_two_affine_line (hφ.comp x hf) ξ]
  exact H

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

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarJetFormula
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

lemma quadratic_expansion_scalar_formula [FiniteDimensional ℝ E] {f:E → ℝ} {p:E} {A:E →L[ℝ] E}
    (hf:HasQuadraticExpansion f p A) (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e))
    {φ:ℝ → ℝ} (hφ:ContDiffAt ℝ 2 φ (f 0)) :
    ∃q:E,∃B:E →L[ℝ] E,(∀d e,inner ℝ (B d) e=inner ℝ d (B e)) ∧
      HasQuadraticExpansion (fun h=>φ (f h)) q B ∧
      ∀d,inner ℝ (B d) d=iteratedDeriv 2 φ (f 0)*(inner ℝ p d)^2+
        deriv φ (f 0)*inner ℝ (A d) d := by
  let P:=quadraticTaylor (f 0) p A
  have hP:ContDiff ℝ 2 P := by
    dsimp only [P,quadraticTaylor]
    exact (contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).add
      ((A.contDiff.inner ℝ contDiff_id).div_const 2)
  have hp0:P 0=f 0 := by simp only [P,quadraticTaylor,map_zero,inner_zero_right,zero_div,add_zero]
  have hQ:ContDiffAt ℝ 2 (fun h=>φ (P h)) 0 := (hp0.symm ▸ hφ).comp 0 hP.contDiffAt
  have H:=quadratic_expansion_scalar_proxy hf hφ
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun h=>φ (P h)) 0),
    bilinearOperator (fderiv ℝ (fderiv ℝ (fun h=>φ (P h))) 0),?_,?_,?_⟩
  · intro d e
    rw [bilinearOperator_inner]
    calc
      _ = fderiv ℝ (fderiv ℝ (fun h=>φ (P h))) 0 e d :=
        (hQ.isSymmSndFDerivAt (by norm_num)).eq d e
      _ = _ := by rw [real_inner_comm,bilinearOperator_inner]
  · intro epsilon hepsilon
    obtain ⟨radius,hradius,hball⟩ := Metric.eventually_nhds_iff.mp (H.eventually hepsilon)
    refine ⟨radius,hradius,?_⟩
    intro vector hvector
    have hbound := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hvector)
    simpa only [P,quadraticTaylor,bilinearOperator_inner,InnerProductSpace.toDual_symm_apply,
      sub_add_eq_sub_sub] using hbound
  · intro d
    rw [bilinearOperator_inner,second_fderiv_scalar_comp hP.contDiffAt (hp0.symm ▸ hφ),hp0]
    rw [show fderiv ℝ P 0=innerSL ℝ p from by
      simpa only [map_zero,add_zero] using (quadraticTaylor_hasFDerivAt (f 0) p hA 0).fderiv]
    rw [quadraticTaylor_second_fderiv (f 0) p hA]
    rfl
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FiberLog
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_fiber_log {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) :
    ∃ L : M → TangentSpace 𝓘(ℝ,Model n) x,
      ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) ∞ L
        (riemannianExp x p) ∧
      L (riemannianExp x p)=p ∧
      (∀ᶠ y in 𝓝 (riemannianExp x p), riemannianExp x (L y)=y) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  let d := extChartAt 𝓘(ℝ,Model n) y
  obtain ⟨e,he,hpe,hei⟩ := exists_coordinate_exp_inverse hp
  have hep : e p=d y := by rw [he]
  let L : M → V := fun z => e.symm (d z)
  have hL : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L y :=
    (show ContDiffAt ℝ ∞ e.symm (d y) from hep ▸ hei).contMDiffAt.comp y
      (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y from contMDiffAt_extChartAt)
  have hLy : L y=p := by dsimp [L]; rw [←hep,e.left_inv hpe]
  refine ⟨L,hL,hLy,?_⟩
  have ht : ∀ᶠ z in 𝓝 y, d z∈e.target :=
    (continuousAt_extChartAt y).eventually
      ((e.open_target.mem_nhds (hep ▸ e.map_source hpe)))
  have hcont : ContinuousAt (fun z => riemannianExp x (L z)) y :=
    (continuous_riemannianExp x).continuousAt.comp hL.continuousAt
  have hs : ∀ᶠ z in 𝓝 y, riemannianExp x (L z)∈d.source := by
    have H := hcont.eventually (show d.source∈𝓝 (riemannianExp x (L y)) from by
      rw [hLy]; exact extChartAt_source_mem_nhds y)
    exact H
  filter_upwards [ht,hs,extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) y] with z hzt hzs hsz
  apply d.injOn hzs hsz
  have HR := e.right_inv hzt
  rw [he] at HR
  exact HR

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

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

lemma HasQuadraticExpansion.hasFDerivAt {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hexp : HasQuadraticExpansion f p A) : HasFDerivAt f ((innerSL ℝ) p) 0 := by
  obtain ⟨d,hd,hbound⟩ := hexp 1 zero_lt_one
  let K : ℝ := 1+‖A‖/2
  have hK : 0 < K := by dsimp [K] <;> positivity
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro c hc
  have hpos : 0 < min d (c/K) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0:E) hpos] with h hh
  have hn : ‖h‖ < min d (c/K) := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  have hb := hbound h (lt_of_lt_of_le hn (min_le_left _ _))
  have hA : |inner ℝ (A h) h| ≤ ‖A‖*‖h‖^2 := by
    calc
      _ ≤ ‖A h‖*‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A‖*‖h‖)*‖h‖ := mul_le_mul_of_nonneg_right (A.le_opNorm h) (norm_nonneg _)
      _ = _ := by ring
  have heq : f h-f 0-inner ℝ p h =
      (f h-quadraticTaylor (f 0) p A h)+inner ℝ (A h) h/2 := by
    simp only [quadraticTaylor]
    ring
  have hb' : |f h-f 0-inner ℝ p h| ≤ K*‖h‖^2 := by
    rw [heq]
    have ht := abs_add_le (f h-quadraticTaylor (f 0) p A h) (inner ℝ (A h) h/2)
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
    dsimp [K]
    nlinarith
  have hmul : ‖h‖*K ≤ c := (le_div_iff₀ hK).mp (le_of_lt (lt_of_lt_of_le hn (min_le_right _ _)))
  have hbc : K*‖h‖^2 ≤ c*‖h‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hmul (norm_nonneg h)]
  simpa only [zero_add,innerSL_apply_apply,Real.norm_eq_abs] using hb'.trans hbc

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_TrueCenterGradient
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

lemma quadratic_scalar_gradient {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f:E → ℝ} {p s:E} {A S:E →L[ℝ] E}
    (hf:HasQuadraticExpansion f p A) {φ:ℝ → ℝ} {l:ℝ}
    (hφ:HasDerivAt φ l (f 0))
    (hS:HasQuadraticExpansion (fun h=>φ (f h)) s S) : s=l • p := by
  have H:=hS.hasFDerivAt.unique (hφ.comp_hasFDerivAt 0 hf.hasFDerivAt)
  apply ext_inner_right ℝ
  intro d
  have HH:=congrArg (fun L:E →L[ℝ] ℝ=>L d) H
  simpa only [innerSL_apply_apply,smul_apply,smul_eq_mul,
    real_inner_smul_left] using HH

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalLowerTaylorBound
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

lemma reverse_normal_pairing {a b : M}
    {p : TangentSpace 𝓘(ℝ,Model n) a} {q : TangentSpace 𝓘(ℝ,Model n) b}
    (hp : p∈injectivityDomain a) (hq : q∈injectivityDomain b)
    (hpq : riemannianExp a p=b)
    {R : TangentSpace 𝓘(ℝ,Model n) b → TangentSpace 𝓘(ℝ,Model n) a}
    (hR : DifferentiableAt ℝ R q) (hR0 : R q=0)
    (hRe : ∀ᶠ w in 𝓝 q,riemannianExp a (R w)=riemannianExp b w)
    (w : TangentSpace 𝓘(ℝ,Model n) b) :
    inner ℝ p (fderiv ℝ R q w)=-inner ℝ q w := by
  have heq : (fun v => normalCost a p (R v)) =ᶠ[𝓝 q] (fun v => ‖v‖^2/2) := by
    filter_upwards [hRe,(isOpen_injectivityDomain b).mem_nhds hq] with v hv hvreg
    dsimp only [normalCost]
    rw [hv,hpq]
    change dist (riemannianExp b v) b^2/2=‖v‖^2/2
    rw [dist_comm,injectivityDomain_subset_minimizingVectors b hvreg]
  have hg : HasFDerivAt (normalCost a p) (innerSL ℝ (-p)) (R q) := by
    rw [hR0]; exact normalCost_hasFDerivAt_zero hp
  have hh : HasFDerivAt (fun v : TangentSpace 𝓘(ℝ,Model n) b => ‖v‖^2/2)
      (innerSL ℝ q) q := by
    convert! ((hasStrictFDerivAt_norm_sq q).hasFDerivAt.const_mul (1/2:ℝ)) using 1
    · ext v; ring
    · ext v
      simp only [smul_apply,smul_eq_mul]
      ring
  have H : (innerSL ℝ (-p)).comp (fderiv ℝ R q)=innerSL ℝ q :=
    ((hg.comp q hR.hasFDerivAt).congr_of_eventuallyEq heq.symm).unique hh
  have HV := congrArg (fun A => A w) H
  simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,inner_neg_left] at HV
  linarith only [HV]

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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ContactDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section ContactDifferential
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf
omit [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma inner_normalHessianOperator (x : M) (p u v : TangentSpace 𝓘(ℝ,Model n) x) :
    inner ℝ (normalHessianOperator x p u) v=normalHessian x p u v := by
  exact InnerProductSpace.toDual_symm_apply

end ContactDifferential
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_FixedJoinSpectrum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
section FixedJoinSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]

local instance tangentFiniteSpectrum_rdfcad4_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma tangent_finrank (x : M) : finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x)=n :=
  finrank_euclideanSpace_fin
end FixedJoinSpectrum
end WeakMTWTransport

end

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

lemma abs_det_hessian_pullback (B:E →L[ℝ] F) (W:F →L[ℝ] F)
    (hd:Module.finrank ℝ E=Module.finrank ℝ F) :
    |(B.adjoint.comp (W.comp B)).det|=B.toLinearMap.normDet^2*|W.det| := by
  have h1:=LinearMap.normDet_comp_of_finrank_eq B.toLinearMap W.toLinearMap hd
  have h2:=LinearMap.normDet_comp_of_finrank_eq (W.comp B).toLinearMap B.adjoint.toLinearMap hd
  have h3:=LinearMap.normDet_comp_of_finrank_eq B.toLinearMap B.adjoint.toLinearMap hd
  have hs:(B.adjoint.comp B).det=B.toLinearMap.normDet^2:=by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using B.normDet_sq.symm
  rw [LinearMap.normDet_eq_abs_det] at h2 h3
  change |(B.adjoint.comp B).det|=B.adjoint.toLinearMap.normDet*B.toLinearMap.normDet at h3
  rw [hs,abs_of_nonneg (sq_nonneg _)] at h3
  rw [LinearMap.normDet_eq_abs_det] at h1
  change |(B.adjoint.comp (W.comp B)).det|=_ at h2
  rw [h2]
  change B.adjoint.toLinearMap.normDet*(W.comp B).toLinearMap.normDet=_
  rw [show (W.comp B).toLinearMap.normDet=|W.det| *B.toLinearMap.normDet from h1]
  calc
    _ = (B.adjoint.toLinearMap.normDet*B.toLinearMap.normDet)*|W.det| := by ring
    _ = _ := by rw [←h3]

omit [CompleteSpace E] in
lemma symmetric_det_pos {A:E →L[ℝ] E}
    (hA:∀x y,inner ℝ (A x) y=inner ℝ x (A y))
    (hp:∀x,x≠0 → 0 < inner ℝ (A x) x) : 0<A.det := by
  have hs:A.toLinearMap.IsSymmetric:=hA
  change 0<A.toLinearMap.det
  rw [hs.det_eq_prod_eigenvalues rfl]
  exact Finset.prod_pos (fun i _=>symmetric_eigenvalue_pos hs rfl hp i)

lemma det_positive_hessian_pullback {B:E →L[ℝ] F} {W:F →L[ℝ] F}
    (hd:Module.finrank ℝ E=Module.finrank ℝ F) (hi:Function.Injective B)
    (hW:∀x y,inner ℝ (W x) y=inner ℝ x (W y))
    (hp:∀x,x≠0 → 0 < inner ℝ (W x) x) {l:ℝ} (hl:0<l) :
    (∀d,d≠0 → 0 < inner ℝ ((l • (B.adjoint.comp (W.comp B))) d) d) ∧
    (l • (B.adjoint.comp (W.comp B))).det=
      l^Module.finrank ℝ E*B.toLinearMap.normDet^2*W.det := by
  have hs:∀x y,inner ℝ ((l • (B.adjoint.comp (W.comp B))) x) y=
      inner ℝ x ((l • (B.adjoint.comp (W.comp B))) y):=by
    intro x y
    simp only [smul_apply,ContinuousLinearMap.comp_apply,
      real_inner_smul_left,real_inner_smul_right,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right,hW]
  have hpos:∀d,d≠0 → 0 < inner ℝ ((l • (B.adjoint.comp (W.comp B))) d) d := by
    intro d hd
    simp only [smul_apply,ContinuousLinearMap.comp_apply,
      real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left]
    exact mul_pos hl (hp _ (fun h=>hd (hi (h.trans B.map_zero.symm))))
  refine ⟨hpos,?_⟩
  have H:=abs_det_hessian_pullback B W hd
  have hpull:0<(B.adjoint.comp (W.comp B)).det:=by
    apply symmetric_det_pos
    · intro x y
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.adjoint_inner_right,hW]
    · intro d hd
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
      exact hp _ (fun h=>hd (hi (h.trans B.map_zero.symm)))
  rw [abs_of_pos hpull,abs_of_pos (symmetric_det_pos hW hp)] at H
  change (l • (B.adjoint.comp (W.comp B)).toLinearMap).det=_
  rw [LinearMap.det_smul]
  change l^Module.finrank ℝ E*(B.adjoint.comp (W.comp B)).det=_
  rw [H]
  ring
end PullbackDet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_UniformJacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exp_mfderiv_zero_apply (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) 0 v=v := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have heq : (fun t : ℝ => riemannianExp x (t • v))=
      (fun t : ℝ => (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :=
    funext (riemannianExp_smul x v)
  have hf : HasFDerivAt (fun t : ℝ => t • v) ((1 : ℝ →L[ℝ] ℝ).smulRight v) 0 :=
    ((1 : ℝ →L[ℝ] ℝ).smulRight v).hasFDerivAt
  have H := mfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,V))
    (I'' := 𝓘(ℝ,Model n)) (0:ℝ)
    ((contMDiff_riemannianExp_fiber x (0 • v)).mdifferentiableAt (by simp))
    hf.differentiableAt.mdifferentiableAt (1:ℝ)
  have hv := spray_velocity_eq_mfderiv ((sprayFlow_curve
    (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).isMIntegralCurveAt (0:ℝ))
  simp only [Function.comp_def,mfderiv_eq_fderiv,hf.fderiv] at H
  rw [heq] at H
  rw [sprayFlow_zero] at hv
  have hz : (0:ℝ) • v=(0:V) := zero_smul ℝ v
  have h1 : ((1 : ℝ →L[ℝ] ℝ).smulRight v) (1:ℝ)=v := by simp
  erw [hz,h1] at H
  exact H.symm.trans hv

end WeakMTWTransport

end



noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.tangentFiniteExpJac
lemma normal_endpoint_derivative_eq {x y : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hL : DifferentiableAt ℝ L p) (hLp : L p=0)
    (hLi : ∀ᶠ v in 𝓝 p, riemannianExp y (L v)=riemannianExp x v)
    (k : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ L p k=mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) p k := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let W := TangentSpace 𝓘(ℝ,Model n) y
  have H := mfderiv_comp_apply_of_eq (I := 𝓘(ℝ,V)) (I' := 𝓘(ℝ,W))
    (I'' := 𝓘(ℝ,Model n)) p
    ((contMDiff_riemannianExp_fiber y 0).mdifferentiableAt (by simp))
    hL.mdifferentiableAt hLp k
  erw [mfderiv_eq_fderiv,exp_mfderiv_zero_apply] at H
  have HC := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ,V)) (I' := 𝓘(ℝ,Model n))
    (show riemannianExp y ∘ L =ᶠ[𝓝 p] riemannianExp x from hLi)
  have HC' := congrArg (fun A => A k) HC
  exact H.symm.trans HC'

lemma expJacobian_eq_normal_endpoint {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p)}
    (hL : DifferentiableAt ℝ L p) (hLp : L p=0)
    (hLi : ∀ᶠ v in 𝓝 p, riemannianExp (riemannianExp x p) (L v)=riemannianExp x v) :
    expJacobian x p=(fderiv ℝ L p).toLinearMap.normDet := by
  unfold expJacobian
  apply congrArg LinearMap.normDet
  ext k
  exact (normal_endpoint_derivative_eq hL hLp hLi k).symm

lemma exists_normal_endpoint_coordinates (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    ∃ L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p),
      ContDiffAt ℝ ∞ L p ∧ L p=0 ∧
      (∀ᶠ v in 𝓝 p, riemannianExp (riemannianExp x p) (L v)=riemannianExp x v) := by
  let y := riemannianExp x p
  obtain ⟨N,hN,hN0,hNi⟩ := exists_smooth_fiber_log (zero_mem_injectivityDomain (n := n) y)
  simp only [riemannianExp_zero] at hN hN0 hNi
  refine ⟨(fun v => N (riemannianExp x v)),?_,hN0,?_⟩
  · exact (hN.comp p (contMDiff_riemannianExp_fiber x p)).contDiffAt
  · exact (continuous_riemannianExp x).continuousAt.eventually hNi
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_TrueCenterMatrix
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
section TrueCenterMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.tangentFiniteTrue
attribute [local instance] OAI.WeakMTWTransport.tangentCompleteTrue
omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma normal_contact_matrix_symmetric {u:M → ℝ} {y:M}
    {p:TangentSpace 𝓘(ℝ,Model n) y}
    {A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hA:NormalAlexandrovContact (n:=n) u y p A) :
    ∀d e,inner ℝ ((normalHessianOperator y p+A) d) e=
      inner ℝ d ((normalHessianOperator y p+A) e) := by
  intro d e
  simp only [add_apply,inner_add_left,inner_add_right,
    inner_normalHessianOperator,hA.2.2.1]
  rw [←real_inner_comm d (normalHessianOperator y p e),inner_normalHessianOperator,
    normalHessian_symm hA.2.1 d e]

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma normal_endpoint_derivative_injective {x y:M}
    {q:TangentSpace 𝓘(ℝ,Model n) x} (hq:q∈injectivityDomain x)
    {R:TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hR:DifferentiableAt ℝ R q) (hR0:R q=0)
    (hRe:∀ᶠ v in 𝓝 q,riemannianExp y (R v)=riemannianExp x v) :
    Function.Injective (fderiv ℝ R q) := by
  have hy:y=riemannianExp x q:=by
    have H:=hRe.self_of_nhds
    simpa only [hR0,riemannianExp_zero] using H
  subst y
  have hi:Function.Injective (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
    (riemannianExp x) q):=(expJacobian_ne_zero_iff x q).mp
      (expJacobian_pos_of_injectivityDomain hq).ne'
  intro a b hab
  apply hi
  simpa only [←normal_endpoint_derivative_eq hR hR0 hRe] using hab

omit [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma normal_scalar_chain_pullback {x y:M}
    {p:TangentSpace 𝓘(ℝ,Model n) y}
    {A S:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    {l dd:ℝ} (hl:0<l)
    {q:TangentSpace 𝓘(ℝ,Model n) x}
    {B:TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hg:∀d,l*inner ℝ p (B d)=-inner ℝ q d)
    (hS:∀d,inner ℝ (S d) d=dd*(inner ℝ p d)^2+l*inner ℝ (A d) d) :
    let V:=l • B.adjoint.comp ((normalHessianOperator y p+A).comp B)
    ∀d,inner ℝ (S (B d)) (B d)+normalHessian y (l • p) (B d) (B d)=
      inner ℝ (V d) d+
      (normalHessian y (l • p) (B d) (B d)-l*normalHessian y p (B d) (B d))+
      (dd/l^2)*(inner ℝ q d)^2 := by
  intro V d
  have hsquare:(inner ℝ p (B d))^2=(inner ℝ q d)^2/l^2:=by
    apply (eq_div_iff (pow_ne_zero _ hl.ne')).mpr
    have hh:=congrArg (fun z:ℝ=>z^2) (hg d)
    simp only [mul_pow,neg_sq] at hh
    simpa only [mul_comm] using hh
  dsimp only [V]
  rw [hS]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left,
    add_apply,inner_add_left,inner_normalHessianOperator]
  rw [hsquare]
  ring

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma true_center_matrix {u:M → ℝ} {x y:M}
    {p:TangentSpace 𝓘(ℝ,Model n) y}
    {A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hA:NormalAlexandrovContact (n:=n) u y p A)
    (hp:∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator y p+A) d) d)
    {q:TangentSpace 𝓘(ℝ,Model n) x} (hq:q∈injectivityDomain x)
    (hxy:riemannianExp x q=y) {l:ℝ} (hl:0<l) (hl1:l<1)
    (hyx:riemannianExp y (l • p)=x) {φ:ℝ → ℝ}
    (hφ:ContDiffAt ℝ 2 φ (cTransform u y)) (hφd:deriv φ (cTransform u y)=l) :
    ∃R:TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y,
    ∃s:TangentSpace 𝓘(ℝ,Model n) y,
    ∃S:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y,
      ContDiffAt ℝ ∞ R q ∧ R q=0 ∧
      (∀ᶠ z in 𝓝 q,riemannianExp y (R z)=riemannianExp x z) ∧
      (∀d e,inner ℝ (S d) e=inner ℝ d (S e)) ∧
      HasQuadraticExpansion (fun h=>φ (cTransform u (riemannianExp y h))) s S ∧
      let B:=fderiv ℝ R q
      let V:=l • B.adjoint.comp ((normalHessianOperator y p+A).comp B)
      (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
      V.det=l^n*(expJacobian x q)^2*(normalHessianOperator y p+A).det ∧
      ∀d,inner ℝ (S (B d)) (B d)+normalHessian y (l • p) (B d) (B d)=
        inner ℝ (V d) d+
        (normalHessian y (l • p) (B d) (B d)-l*normalHessian y p (B d) (B d))+
        (iteratedDeriv 2 φ (cTransform u y)/l^2)*(inner ℝ q d)^2 := by
  subst y
  let y:=riemannianExp x q
  obtain ⟨R,hR,hR0,hRe⟩:=exists_normal_endpoint_coordinates x q
  let B:=fderiv ℝ R q
  have hBd:DifferentiableAt ℝ R q:=hR.differentiableAt (by simp)
  have hBi:Function.Injective B:=normal_endpoint_derivative_injective hq hBd hR0 hRe
  have hWs:=normal_contact_matrix_symmetric hA
  have hdet:=det_positive_hessian_pullback (B:=B) (W:=normalHessianOperator y p+A) (l:=l)
    ((tangent_finrank x).trans (tangent_finrank y).symm) hBi hWs hp hl
  have hscalar:=quadratic_expansion_scalar_formula (φ:=φ) hA.2.2.2 hA.2.2.1
    (by simpa only [riemannianExp_zero] using hφ)
  obtain ⟨s,S,hS,hSe,hSf⟩:=hscalar
  refine ⟨R,s,S,hR,hR0,hRe,hS,hSe,hdet.1,?_,?_⟩
  · rw [hdet.2,tangent_finrank x]
    rw [expJacobian_eq_normal_endpoint hBd hR0 hRe]
  · apply normal_scalar_chain_pullback hl
    · intro d
      have hpr:l • p∈injectivityDomain y:=contracted_minimizer_mem_injectivityDomain
        (injectivityDomain_subset_minimizingVectors y hA.2.1) hl hl1
      simpa only [real_inner_smul_left] using
        reverse_normal_pairing hpr hq hyx hBd hR0 hRe d
    · simpa only [riemannianExp_zero,hφd] using hSf
end TrueCenterMatrix
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartTrueCenter
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
section ChartTrueCenter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance chartTrueFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma chart_true_center_matrix {u:M → ℝ} {a c y:M} {b q:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hq:chartFiberInverse a b q∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hy:movingPrefix a 1 b q=y) (hc:y∈(extChartAt 𝓘(ℝ,Model n) c).source)
    {p:TangentSpace 𝓘(ℝ,Model n) y}
    {A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hA:NormalAlexandrovContact (n:=n) u y p A)
    (hp:∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator y p+A) d) d)
    {l:ℝ} (hl:0<l) (hl1:l<1)
    (hpx:riemannianExp y (l • p)=(extChartAt 𝓘(ℝ,Model n) a).symm b)
    {φ:ℝ → ℝ} (hφ:ContDiffAt ℝ 2 φ (cTransform u y))
    (hφd:deriv φ (cTransform u y)=l)
    {s:Model n} {S:Model n →L[ℝ] Model n}
    (hS:∀d e,inner ℝ (S d) e=inner ℝ d (S e))
    (hSe:HasQuadraticExpansion (fun h=>φ (cTransform u
      ((extChartAt 𝓘(ℝ,Model n) c).symm (extChartAt 𝓘(ℝ,Model n) c y+h)))) s S) :
    ∃ R:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b) →
      TangentSpace 𝓘(ℝ,Model n) y,
    ∃ V:Model n →L[ℝ] Model n,
      DifferentiableAt ℝ R (chartFiberInverse a b q) ∧ R (chartFiberInverse a b q)=0 ∧
      (∀ᶠ z in 𝓝 (chartFiberInverse a b q),riemannianExp y (R z)=
        riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) z) ∧
      (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
      (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
      V.det=(chartFiberInverse a b).toLinearMap.normDet^2*l^n*
        (expJacobian ((extChartAt 𝓘(ℝ,Model n) a).symm b) (chartFiberInverse a b q))^2*
        (normalHessianOperator y p+A).det ∧
      ∀d,chartJetMatrix a c b q (innerSL ℝ s) ((innerSL ℝ).comp S) d d=
        inner ℝ (V d) d+
        (normalHessian y (l • p)
          (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))
          (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))-
         l*normalHessian y p
          (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))
          (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d)))+
        (iteratedDeriv 2 φ (cTransform u y)/l^2)*
          (inner ℝ (chartFiberInverse a b q) (chartFiberInverse a b d))^2 := by
  let x: M := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let B:=chartFiberInverse a b
  have he:riemannianExp x (B q)=y:=by
    simpa only [movingPrefix_eq hb,one_smul,x,B,chartFiberInverse] using hy
  obtain ⟨R,r,T,hR,hR0,hRe,hT,hTe,hV,hVdet,hmat⟩:=
    true_center_matrix hA hp hq he hl hl1 hpx hφ hφd
  let C:=fderiv ℝ R (B q)
  let W:=normalHessianOperator y p+A
  let V0:=l • C.adjoint.comp (W.comp C)
  let V:=B.adjoint.comp (V0.comp B)
  have hWs:=normal_contact_matrix_symmetric hA
  have hV0s:∀d e,inner ℝ (V0 d) e=inner ℝ d (V0 e):=by
    intro d e
    simp only [V0,smul_apply,ContinuousLinearMap.comp_apply,
      real_inner_smul_left,real_inner_smul_right,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
    rw [hWs]
  have hB:Function.Injective B:=by
    exact chartFiberInverse_injective hb
  have hdim:Module.finrank ℝ (Model n)=Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x):=by
    rw [tangent_finrank]
    exact finrank_euclideanSpace_fin
  have hP:=det_positive_hessian_pullback (B:=B) (W:=V0) hdim hB hV0s hV (show (0:ℝ)<1 by norm_num)
  simp only [one_smul,one_pow,one_mul] at hP
  have hr:r=l • p:=quadratic_scalar_gradient hA.2.2.2
    (by simpa only [riemannianExp_zero,hφd] using (hφ.differentiableAt (by norm_num)).hasDerivAt) hTe
  rw [hr] at hTe
  have hpr:l • p∈injectivityDomain y:=contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors y hA.2.1) hl hl1
  have hid:=chartJetMatrix_normal_identity (f:=fun z=>φ (cTransform u z)) hb hq hy hc hpr hpx hTe hS hSe
    (hR.differentiableAt (by simp)) hR0 hRe
  refine ⟨R,V,hR.differentiableAt (by simp),hR0,hRe,?_,hP.1,?_,?_⟩
  · intro d e
    simp only [V,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right,hV0s]
  · change V.det=_
    rw [hP.2]
    change B.toLinearMap.normDet^2*V0.det=_
    rw [hVdet]
    ring
  · intro d
    rw [hid d,hmat (B d)]
    simp only [V,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
    rfl
end ChartTrueCenter
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartCenterGain
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
section ChartCenterGain
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance chartCenterGainFinite_rdfcad4_1 (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma exists_chart_true_center_gain : ∃δ>0,∀ᶠ l:ℝ in 𝓝 1,l<1 → 0<l →
    ∀(u:M → ℝ) (a c y:M) (b q:Model n),
    b∈(extChartAt 𝓘(ℝ,Model n) a).target →
    chartFiberInverse a b q∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b) →
    movingPrefix a 1 b q=y → y∈(extChartAt 𝓘(ℝ,Model n) c).source →
    ∀p:TangentSpace 𝓘(ℝ,Model n) y,
    ∀A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y,
    NormalAlexandrovContact (n:=n) u y p A →
    (∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator y p+A) d) d) →
    riemannianExp y (l • p)=(extChartAt 𝓘(ℝ,Model n) a).symm b →
    ∀φ:ℝ → ℝ,ContDiffAt ℝ 2 φ (cTransform u y) → deriv φ (cTransform u y)=l →
    ∀s:Model n,∀S:Model n →L[ℝ] Model n,
    (∀d e,inner ℝ (S d) e=inner ℝ d (S e)) →
    HasQuadraticExpansion (fun h=>φ (cTransform u ((extChartAt 𝓘(ℝ,Model n) c).symm
      (extChartAt 𝓘(ℝ,Model n) c y+h)))) s S →
    ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (bilinearOperator V).det=(chartFiberInverse a b).toLinearMap.normDet^2*l^n*
        (expJacobian ((extChartAt 𝓘(ℝ,Model n) a).symm b) (chartFiberInverse a b q))^2*
        (normalHessianOperator y p+A).det ∧
      ∀d,V d d+δ*(1-l)*frameMetric a b d d+
        (iteratedDeriv 2 φ (cTransform u y)/l^2)*(frameMetric a b q d)^2≤
          chartJetMatrix a c b q (innerSL ℝ s) ((innerSL ℝ).comp S) d d := by
  obtain ⟨δ,hδ,Hδ⟩:=exists_uniform_true_center_gain (n:=n) (M:=M)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [Hδ] with l hl
  intro hl1 hl0 u a c y b q hb hq hy hc p A hA hp hpx φ hφ hφd s S hS hSe
  obtain ⟨R,V,hR,hR0,hRe,hVs,hVp,hVdet,hmat⟩:=
    chart_true_center_matrix hb hq hy hc hA hp hl0 hl1 hpx hφ hφd hS hSe
  let VB:Model n →L[ℝ] Model n →L[ℝ] ℝ:=(innerSL ℝ).comp V
  have hVB:bilinearOperator VB=V:=by
    apply ContinuousLinearMap.ext
    intro d
    apply ext_inner_right ℝ
    intro e
    rw [bilinearOperator_inner]
    rfl
  refine ⟨VB,?_,?_,?_,?_⟩
  · intro d e
    change inner ℝ (V d) e=inner ℝ (V e) d
    rw [hVs,real_inner_comm]
  · exact hVp
  · rwa [hVB]
  · intro d
    have he:riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) (chartFiberInverse a b q)=y:=by
      simpa only [movingPrefix_eq hb,one_smul,chartFiberInverse] using hy
    have HG:=hl hl1 ((extChartAt 𝓘(ℝ,Model n) a).symm b) (chartFiberInverse a b q)
    rw [he] at HG
    have HH:=HG p hA.2.1 hq hpx R hR hR0 hRe (chartFiberInverse a b d)
    rw [hmat,frameMetric_apply hb,frameMetric_apply hb,real_inner_self_eq_norm_sq]
    dsimp only [VB,ContinuousLinearMap.comp_apply,innerSL_apply_apply]
    linarith only [HH]
end ChartCenterGain
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_TrueCenterJet
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
section TrueCenterJet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance trueCenterJetFinite_rdfcad4_1 (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma exists_true_center_jet_gain_oai : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀l∈U,0<l → l<1 → ∀(u:M → ℝ) (a c:M) (φ:ℝ → ℝ),
    ∀J:TrueCenterJet (n:=n) u a c φ l,
    ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (bilinearOperator V).det=(chartFiberInverse a J.b).toLinearMap.normDet^2*l^n*
        (expJacobian J.shortRay.1 J.shortRay.2)^2*(normalHessianOperator J.y J.p+J.A).det ∧
      ∀d,V d d+δ*(1-l)*frameMetric a J.b d d+
        (J.curvature/l^2)*(frameMetric a J.b J.q d)^2≤J.matrix d d := by
  obtain ⟨δ,hδ,Hδ⟩:=exists_chart_true_center_gain (n:=n) (M:=M)
  obtain ⟨U,hU,hUo,h1⟩:=mem_nhds_iff.mp Hδ
  refine ⟨δ,hδ,U,hUo,h1,?_⟩
  intro l hl hl0 hl1 u a c φ J
  exact hU hl hl1 hl0 u a c J.y J.b J.q J.chart J.regular J.endpoint
    J.endChart J.p J.A J.original J.positive J.pole φ J.smooth J.slope J.s J.S
    J.symmetric J.expansion

end TrueCenterJet
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.exists_true_center_jet_gain_oai.{u_1} := @OAI.WeakMTWTransport.exists_true_center_jet_gain_oai.{u_1}
