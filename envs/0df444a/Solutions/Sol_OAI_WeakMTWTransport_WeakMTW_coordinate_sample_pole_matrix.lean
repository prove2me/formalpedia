-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.coordinate_sample_pole_matrix
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:37:50.520272+00:00
-- url     : https://prove2.me/submissions/4b105e8f-dab3-42e8-9591-0472261d468e

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
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_actual_sample_pole_matrix

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_LowerTaylorComposition
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HasLowerSecondTaylor.comp_stationary {f : F → ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hf : HasLowerSecondTaylor f 0 B)
    {a : E → F} {A : E →L[ℝ] F} (ha : HasFDerivAt a A 0) (ha0 : a 0=0) :
    HasLowerSecondTaylor (fun h => f (a h)) 0 (pullBilinear B A) := by
  have hO : a =O[𝓝 0] (fun h : E => h) := by
    simpa only [ha0,sub_zero] using ha.isBigO_sub
  obtain ⟨C,hC,HC⟩ := hO.exists_pos
  have ht : Tendsto a (𝓝 0) (𝓝 0) := ha0 ▸ ha.continuousAt
  intro ε hε
  have hδ : 0 < ε/(2*C^2) := div_pos hε (by positivity)
  have hB := (bilinear_remainder_of_hasFDerivAt ha ha0 B).def hε
  filter_upwards [ht.eventually (hf _ hδ),HC.bound,hB] with h hh haB hb
  simp only [zero_apply,add_zero] at hh ⊢
  rw [ha0,pullBilinear_apply]
  have hb' : |B (a h) (a h)-B (A h) (A h)| ≤ ε*‖h‖^2 := by
    simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using hb
  have hsq : ‖a h‖^2 ≤ C^2*‖h‖^2 := by
    nlinarith only [sq_nonneg (C*‖h‖-‖a h‖),haB,norm_nonneg (a h),
      mul_nonneg hC.le (norm_nonneg h)]
  have hsq' := mul_le_mul_of_nonneg_left hsq (le_of_lt hδ)
  have he : ε/(2*C^2)*(C^2*‖h‖^2)=(ε/2)*‖h‖^2 := by
    field_simp [hC.ne']
  rw [he] at hsq'
  linarith only [hh,(abs_le.mp hb').1,hsq']

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
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_ActualPole
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

lemma WeakMTW.prefix_hopfLax_differentiable (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (x:M) :
    Differentiable ℝ (fun q : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • q))) := by
  intro q
  have he := (contMDiff_riemannianExp_fiber (n := n) x (t • q)).mdifferentiableAt (by simp)
  have hl : MDifferentiableAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x)
      𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) (fun q => t • q) q :=
    (show ContDiffAt ℝ ∞ (fun q : TangentSpace 𝓘(ℝ,Model n) x => t • q) q from by
      fun_prop).contMDiffAt.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact ((hmtw.mdifferentiable_hopfLax hu hv hdual ht ht1 _).comp q
    (he.comp q hl)).differentiableAt

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_RoughLinear
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
lemma second_fderiv_comp_linear_at {f : F → ℝ} (L : E →L[ℝ] F) {x : E}
    (hnear : ∀ᶠ y in 𝓝 (L x),DifferentiableAt ℝ f y)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (L x)) (d e : E) :
    fderiv ℝ (fderiv ℝ (fun q=>f (L q))) x d e=
      fderiv ℝ (fderiv ℝ f) (L x) (L d) (L e) := by
  have hl : (fderiv ℝ L)=(fun _ : E=>L) := by funext q; exact L.fderiv
  have H := second_fderiv_comp_at hnear hf (L.contDiff (n := 2)).contDiffAt d e
  rw [hl] at H
  have hz : fderiv ℝ (fun _ : E => L) x = 0 := fderiv_const_apply L
  rw [hz] at H
  simpa using H
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinatePole
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

lemma WeakMTW.coordinate_sample_pole_matrix_oai (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {a c d : M} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈normalSubdifferential (n := n)
        (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hz : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hx : (extChartAt 𝓘(ℝ,Model n) a).symm b∈(extChartAt 𝓘(ℝ,Model n) d).source)
    (hD : DifferentiableAt ℝ
      (fun w : Model n => extChartAt 𝓘(ℝ,Model n) d
        (hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
      (extChartAt 𝓘(ℝ,Model n) c (movingPrefix a t b p))) :
    let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
    let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
    let L := coordinatePoleMatrix a t v b p
    (∀ r:Model n,0≤L r r) ∧ (∀ r s:Model n,L r s=L s r) ∧
    (∀ q:Model n,A q∈activeLogs v x → ∀ r:Model n,L (q-p) r=0) ∧
    (∀ (ι:Type) [Fintype ι] (pj:ι → Model n) (w:ι → ℝ),
      (∀ j,0≤w j) → (∑ j,w j=1) → (∑ j,w j • pj j=p) →
      (∀ j,A (pj j)∈activeLogs v x) → ∀ i,0<w i →
      HasLowerSecondTaylor (fun r:Model n=>v (movingNormal a (b,pj i+r))+
        ‖A (pj i+r)‖^2/2) 0 (w i • L)) := by
  dsimp only
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let I : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
  let f : V → ℝ := fun q=>hopfLax t (cTransform v) (riemannianExp x (t • q))
  let L₀ : V →L[ℝ] V →L[ℝ] ℝ := t • I-fderiv ℝ (fderiv ℝ f) (A p)
  have hz' : riemannianExp x (t • A p)∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    simpa only [movingPrefix_eq hb] using hz
  have hD' : DifferentiableAt ℝ
      (fun w:Model n=>extChartAt 𝓘(ℝ,Model n) d
        (hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
      (extChartAt 𝓘(ℝ,Model n) c (riemannianExp x (t • A p))) := by
    simpa only [movingPrefix_eq hb] using hD
  obtain ⟨hfd,hpos,hsym,hker,hjet⟩ := hmtw.actual_sample_pole_matrix hv ht ht1 hp hz' hx hD'
  have hpre := hmtw.active_hull_precut hv ht ht1 x (A p)
    (normalSubdifferential_subset_active_hull hv x hp)
  have hnear : ∀ᶠ q in 𝓝 (A p),DifferentiableAt ℝ f q :=
    Filter.Eventually.of_forall (fun q=>hmtw.prefix_hopfLax_differentiable
      (continuous_cTransform hv) (continuous_cTransform (continuous_cTransform hv))
      ⟨(cTransform_triple hv).symm,rfl⟩ ht ht1 x q)
  have he : coordinatePoleMatrix a t v b p=pullBilinear L₀ A := by
    ext r s
    have hf : (fun q=>hopfLax t (cTransform v) (movingPrefix a t b q))=(fun q=>f (A q)) := by
      funext q
      exact congrArg (hopfLax t (cTransform v)) (movingPrefix_eq hb t q)
    rw [coordinatePoleMatrix,sub_apply,sub_apply,movingPrefixEnergy_hessian hb hpre,hf,
      second_fderiv_comp_linear_at A hnear hfd,pullBilinear_apply]
    rfl
  rw [he]
  refine ⟨fun r=>hpos (A r),fun r s=>hsym (A r) (A s),?_,?_⟩
  · intro q hq r
    change L₀ (A (q-p)) (A r)=0
    rw [map_sub]
    exact hker (A q) hq (A r)
  · intro ι _ pj w hw hw1 hbar ha i hi
    have hbar' : ∑ i,w i • A (pj i)=A p := by
      simpa only [map_sum,map_smul] using congrArg A hbar
    have H := hjet ι (fun j=>A (pj j)) w hw hw1 hbar' ha i hi
    have H' := H.comp_stationary (A.hasFDerivAt (x := 0)) (map_zero A)
    have heB : pullBilinear (w i • L₀) A=w i • pullBilinear L₀ A := by
      ext r s
      rfl
    rw [heB] at H'
    convert H' using 1
    all_goals try with_reducible_and_instances rfl
    funext r
    simp only [movingNormal_eq hb,map_add]
    rfl

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.coordinate_sample_pole_matrix_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.coordinate_sample_pole_matrix_oai.{u_1}
