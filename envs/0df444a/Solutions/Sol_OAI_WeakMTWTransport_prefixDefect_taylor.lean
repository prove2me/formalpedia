-- Prove2me | solution 1 for OAI.WeakMTWTransport.prefixDefect_taylor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:27:06.001099+00:00
-- url     : https://prove2.me/submissions/59cf18c4-cf64-4db2-9bdd-8016ccf1cb60

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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_LowerTaylor
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HasSecondTaylor.comp_linear {f : F → ℝ} {l : F →L[ℝ] ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) (A : E →L[ℝ] F) :
    HasSecondTaylor (fun h => f (A h)) (l.comp A) (pullBilinear B A) := by
  have H := (hf.comp_tendsto (show Tendsto A (𝓝 0) (𝓝 0) by
    simpa only [ContinuousAt,map_zero] using (A.continuous.continuousAt (x := (0:E))))).trans_isBigO
      ((A.isBigO_id (𝓝 0)).norm_left.norm_right.pow 2)
  simpa only [HasSecondTaylor,map_zero,Function.comp_def,ContinuousLinearMap.comp_apply,
    pullBilinear_apply] using H

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

lemma prefixAction_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x) :
    ContDiffAt ℝ ∞ (prefixAction x t) (0,p) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have he := contMDiff_riemannianExp_fiber (n := n) x
  have hu : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x q.1) (0,p) :=
    (he _).comp (0,p) contDiffAt_fst.contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x (t • q.2)) (0,p) :=
    (he _).comp (0,p) (show ContDiffAt ℝ ∞ (fun q : V×V => t • q.2) (0,p) from by fun_prop).contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨x,t • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:V),riemannianExp x (t • p)) := by
    simpa only [riemannianExp_zero] using hc
  exact ((hc'.comp (0,p) (hu.prodMk hv)).contDiffAt.div_const t)

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

lemma prefixAction_source_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hp : t • p ∈ injectivityDomain x)
    (a : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (prefixAction x t) (0,p) (a,0) = -inner ℝ p a := by
  have hnc := ((normalCost_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have H := hnc.mul_const t⁻¹
  have hp₀ := (hasFDerivAt_id (𝕜 := ℝ) (0 : TangentSpace 𝓘(ℝ,Model n) x)).prodMk
    (hasFDerivAt_const p (0 : TangentSpace 𝓘(ℝ,Model n) x))
  have H' : HasFDerivAt (fun u => prefixAction x t (u,p))
      (t⁻¹ • fderiv ℝ (normalCost x (t • p)) 0) 0 := by
    simpa only [prefixAction,normalCost,div_eq_mul_inv] using H
  have hB := (prefixAction_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heq := (hB.hasFDerivAt.comp (f := fun u => (u,p)) 0 hp₀).unique H'
  have hh := congrArg (fun A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => A a) heq
  change fderiv ℝ (prefixAction x t) (0,p) (a,0) =
    t⁻¹ * fderiv ℝ (normalCost x (t • p)) 0 a at hh
  rw [normalCost_fderiv_zero hp,real_inner_smul_left] at hh
  rw [hh]
  field_simp

lemma prefixAction_mixed {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hp : t • p ∈ injectivityDomain x)
    (a d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (0,d) (a,0) = -inner ℝ d a := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hL : HasFDerivAt (fun v : V => ((0:V),v))
      ((0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)) p :=
    (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := (((hC.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun v : V => ((0:V),v)) p hL).clm_apply
      (hasFDerivAt_const (a,(0:V)) p)
  have heq : (fun v : V => fderiv ℝ (prefixAction x t) (0,v) (a,0)) =ᶠ[𝓝 p]
      (fun v => -inner ℝ v a) := by
    have hn := (continuous_const_smul t).continuousAt.eventually
      ((isOpen_injectivityDomain x).mem_nhds hp)
    filter_upwards [hn] with v hv
    exact prefixAction_source_gradient ht hv a
  have hi : HasFDerivAt (fun v : V => -inner ℝ v a) (-(innerSL ℝ a)) p := by
    convert! ((innerSL ℝ a).hasFDerivAt (x := p)).neg using 1
    all_goals try with_reducible_and_instances rfl
    funext v; exact congrArg Neg.neg (real_inner_comm a v)
  have H := congrArg (fun A : V →L[ℝ] ℝ => A d)
    ((hd.congr_of_eventuallyEq heq.symm).unique hi)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,zero_apply,map_zero,add_zero,zero_add,add_apply,
    ContinuousLinearMap.comp_zero,Function.comp_apply,
    ContinuousLinearMap.flip_apply,neg_apply,innerSL_apply_apply,real_inner_comm] using H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PrefixActionJets
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

lemma prefixAction_source_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x)
    (a : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (a,0) (a,0) =
      hessianValue x (t • p) a/t := by
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [←iteratedDeriv_two_affine_line hC (a,0)]
  simp only [prefixAction,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    smul_zero,zero_add,add_zero]
  change iteratedDeriv 2 (fun r : ℝ =>
    cost (riemannianExp x (r • a)) (riemannianExp x (t • p))/t) 0 = _
  rw [iteratedDeriv_div_const]
  rfl

lemma prefixAction_endpoint_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x)
    (d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (prefixAction x t) (0,p) (0,d) = t*inner ℝ p d := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hD := (prefixAction_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hL := (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have H := (hD.hasFDerivAt.comp (f := fun v : V => ((0:V),v)) p hL).congr_of_eventuallyEq
    (prefixAction_axis_near hp).symm
  have he := congrArg (fun A : V →L[ℝ] ℝ => A d)
    (H.unique ((half_norm_sq_hasFDerivAt p).const_smul t))
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    zero_apply,smul_apply,smul_eq_mul,innerSL_apply_apply] at he
  exact he

lemma prefixAction_endpoint_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x)
    (d e : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (0,d) (0,e) = t*inner ℝ d e := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he := ((prefixAction_axis_near hp).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  let L : V →L[ℝ] V×V := (0:V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)
  have H := second_fderiv_comp_affine L 0 p
    (by simpa only [L,ContinuousLinearMap.prod_apply,zero_apply,
      ContinuousLinearMap.id_apply,zero_add] using hC) d e
  simp only [L,ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,zero_add] at H
  rw [←H,he]
  have hg : fderiv ℝ (fun v : V => t*(‖v‖^2/2)) =
      (fun v => t • innerSL ℝ v) := by
    funext v
    exact ((half_norm_sq_hasFDerivAt v).const_smul t).fderiv
  rw [hg]
  have hD : HasFDerivAt (fun v : V => t • innerSL ℝ v) (t • innerSL ℝ) p := by
    convert! ((innerSL ℝ).hasFDerivAt (x := p)).const_smul t using 1
    all_goals try with_reducible_and_instances rfl
  rw [hD.fderiv]
  rfl

lemma prefixAction_hessian_diag {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hp : t • p ∈ injectivityDomain x)
    (a d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (a,d) (a,d) =
      hessianValue x (t • p) a/t-2*inner ℝ a d+t*‖d‖^2 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hsplit : (a,d)=((a,0):V×V)+(0,d) := by simp
  have hsym := (prefixAction_contDiffAt hp).isSymmSndFDerivAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [hsplit]
  simp only [map_add,add_apply]
  rw [prefixAction_source_hessian hp,hsym.eq (a,0) (0,d),
    prefixAction_mixed ht hp,prefixAction_endpoint_hessian hp]
  rw [real_inner_self_eq_norm_sq,real_inner_comm d a]
  ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_FiniteTaylor
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
open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma HasSecondTaylor.const_mul' {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) (c:ℝ) :
    HasSecondTaylor (fun h => c*f h) (c • l) (c • B) := by
  unfold HasSecondTaylor at *
  have he : (fun h => c*f h-c*f 0-(c • l) h-(c • B) h h/2) =
      (fun h => c*(f h-f 0-l h-B h h/2)) := by
    funext h; simp only [smul_apply,smul_eq_mul] <;> ring
  rw [he]
  exact hf.const_mul_left c

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma prefixDefect_taylor_oai {x : M} {t : ℝ} (ht : t≠0)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x) :
    ∃ B : (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ]
      (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ,
      HasSecondTaylor (prefixDefect x t p)
        ((-innerSL ℝ p).comp (ContinuousLinearMap.fst ℝ _ _)) B ∧
      ∀ a d : TangentSpace 𝓘(ℝ,Model n) x,
        B (a,d) (a,d)=hessianValue x (t • p) a/t-2*inner ℝ a d := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let P : V×V →L[ℝ] V := ContinuousLinearMap.snd ℝ V V
  let H : V×V →L[ℝ] V×V →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p)
  let D : V×V →L[ℝ] V×V →L[ℝ] ℝ := H-t • pullBilinear (innerSL ℝ) P
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HN : HasSecondTaylor (fun h:V×V => t*(‖p+P h‖^2/2))
      (t • ((innerSL ℝ p).comp P)) (t • pullBilinear (innerSL ℝ) P) :=
    ((norm_square_hasSecondTaylor p).comp_linear P).const_mul' t
  have HT := (hasSecondTaylor_shift hC).sub HN
  have hlin : fderiv ℝ (prefixAction x t) (0,p)-t • ((innerSL ℝ p).comp P)=
      (-innerSL ℝ p).comp (ContinuousLinearMap.fst ℝ V V) := by
    apply ContinuousLinearMap.ext
    rintro ⟨a,d⟩
    change fderiv ℝ (prefixAction x t) (0,p) (a,d)-t*inner ℝ p d = -inner ℝ p a
    rw [show (a,d)=((a,0):V×V)+(0,d) by simp,map_add,
      prefixAction_source_gradient ht hp,prefixAction_endpoint_gradient hp]
    ring
  rw [hlin] at HT
  refine ⟨D,?_,?_⟩
  · convert! HT using 1
    all_goals try with_reducible_and_instances rfl
    funext h
    rcases h with ⟨a,d⟩
    simp only [prefixDefect,Prod.mk_add_mk,zero_add,P,ContinuousLinearMap.coe_snd']
  · intro a d
    change fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (a,d) (a,d)-t*inner ℝ d d=_
    rw [prefixAction_hessian_diag ht hp,real_inner_self_eq_norm_sq]
    ring

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.prefixDefect_taylor_oai.{u_1} := @OAI.WeakMTWTransport.prefixDefect_taylor_oai.{u_1}
