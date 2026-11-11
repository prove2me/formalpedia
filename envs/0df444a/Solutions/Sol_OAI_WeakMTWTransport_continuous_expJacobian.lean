-- Prove2me | solution 1 for OAI.WeakMTWTransport.continuous_expJacobian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:18:46.55174+00:00
-- url     : https://prove2.me/submissions/93323ebd-8494-4130-a913-6c3e2a0428b0

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
import Definitions.Def_OAIQ232A024

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

local instance tangentFiniteSpectrum_r44e9f5_1 (x : M) :
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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Matrix
open scoped Topology

namespace WeakMTWTransport
section BilinearMatrix
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma bilinearOperator_tendsto {ι:Type*} {l:Filter ι}
    {B:ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:Tendsto B l (𝓝 B₀)) :
    Tendsto (fun i=>bilinearOperator (B i)) l (𝓝 (bilinearOperator B₀)) := by
  have hc:Continuous (fun B:E →L[ℝ] E →L[ℝ] ℝ=>bilinearOperator B):=
    continuous_const.clm_comp continuous_id
  exact hc.continuousAt.tendsto.comp hB

lemma bilinear_det_tendsto {ι:Type*} {l:Filter ι}
    {B:ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:Tendsto B l (𝓝 B₀)) :
    Tendsto (fun i=>(bilinearOperator (B i)).det) l (𝓝 (bilinearOperator B₀).det) := by
  exact ContinuousLinearMap.continuous_det.continuousAt.tendsto.comp (bilinearOperator_tendsto hB)

end BilinearMatrix
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

lemma movingPrefixEnergy_contDiffAt {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingPrefixEnergy a t)) (b,p) := by
  have hA : ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (fun q:Model n×Model n=> movingNormal a (q.1,0)) (b,p) :=
    (movingNormal_contMDiffAt (q := (b,0)) hb).comp (b,p)
      (contDiffAt_fst.prodMk contDiffAt_const).contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm b,
      t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q:M×M=>cost q.1 q.2) (movingNormal a (b,0),movingPrefix a t b p) := by
    simpa only [movingNormal_zero hb,movingPrefix_eq hb] using hC
  exact ((hC'.comp (b,p) (hA.prodMk (movingPrefix_contMDiffAt hb))).contDiffAt.div_const t)

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

omit [Nonempty M] in
lemma frameMetric_continuousAt {a:M} {b:Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) : ContinuousAt (frameMetric a) b := by
  have hp : (1:ℝ) • chartFiberInverse a b 0∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) := by
    simpa only [map_zero,smul_zero] using zero_mem_injectivityDomain
      (n := n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  have H := (ContDiffAt.partial_snd_fderiv_two (movingPrefixEnergy_contDiffAt hb hp)).continuousAt
  exact ContinuousAt.comp (f := fun z:Model n=>(z,(0:Model n))) H
    (show ContinuousAt (fun z:Model n=>(z,(0:Model n))) b from
    continuousAt_id.prodMk continuousAt_const)

end FrameMetric
end WeakMTWTransport

end
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
lemma frameMetric_operator {a:M} {b:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    bilinearOperator (frameMetric a b)=(chartFiberInverse a b).adjoint.comp (chartFiberInverse a b) := by
  apply ContinuousLinearMap.ext
  intro d
  apply ext_inner_right ℝ
  intro e
  rw [bilinearOperator_inner,frameMetric_apply hb]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]

lemma frameMetric_det {a:M} {b:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    (bilinearOperator (frameMetric a b)).det=(chartFiberInverse a b).toLinearMap.normDet^2 := by
  rw [frameMetric_operator hb]
  simpa only [RCLike.ofReal_real_eq_id,id_eq] using (chartFiberInverse a b).normDet_sq.symm

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

lemma frameNormDet_continuousAt {a:M} {b:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContinuousAt (fun z=>(chartFiberInverse a z).toLinearMap.normDet) b := by
  have H:ContinuousAt (fun z=>Real.sqrt (bilinearOperator (frameMetric a z)).det) b := by
    exact Real.continuous_sqrt.continuousAt.tendsto.comp
      (bilinear_det_tendsto (frameMetric_continuousAt hb).tendsto)
  apply H.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target _).mem_nhds hb] with z hz
  rw [frameMetric_det hz,Real.sqrt_sq (LinearMap.normDet_nonneg _)]

end FrameDet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ExpJacContinuity
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
section ExpJacContinuity
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance expJacContFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma frameNormDet_at {a x:M} (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a x)).toLinearMap.normDet=
      ((trivializationAt (Model n) (fun y:M=>TangentSpace 𝓘(ℝ,Model n) y) a).symmL ℝ x).toLinearMap.normDet := by
  exact congrArg (fun y:M=>((trivializationAt (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x) a).symmL ℝ y).toLinearMap.normDet)
      ((extChartAt 𝓘(ℝ,Model n) a).left_inv hx)

lemma expJacobian_coordinate_identity (c z:TangentBundle 𝓘(ℝ,Model n) M)
    (hz:z∈(extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c).source)
    (he:riemannianExp z.1 z.2∈(extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)).source) :
    expJacobian z.1 z.2 *
      (chartFiberInverse c.1 (extChartAt 𝓘(ℝ,Model n) c.1 z.1)).toLinearMap.normDet=
      (chartFiberInverse (riemannianExp c.1 c.2)
        (extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2) (riemannianExp z.1 z.2))).toLinearMap.normDet*
      |(coordinateEndpointVertical c z).det| := by
  let U:=trivializationAt (Model n) (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x) c.1
  let V:=trivializationAt (Model n) (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x) (riemannianExp c.1 c.2)
  let B:=U.symmL ℝ z.1
  let C:=V.symmL ℝ (riemannianExp z.1 z.2)
  let A:=coordinateEndpointVertical c z
  let E:TangentSpace 𝓘(ℝ,Model n) z.1 →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (riemannianExp z.1 z.2):=
    mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n) (riemannianExp z.1) z.2
  have hz':z.1∈(extChartAt 𝓘(ℝ,Model n) c.1).source:=(tangent_chart_source_iff _ _).mp hz
  have hU:z.1∈U.baseSet:=by simpa only [U,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hz'
  have hV:riemannianExp z.1 z.2∈V.baseSet:=by simpa only [V,TangentBundle.trivializationAt_baseSet,extChartAt_source] using he
  have hEB:E.comp B=C.comp A:=by
    apply ContinuousLinearMap.ext
    intro d
    have HH:=coordinateEndpointVertical_apply c z hz he (B d)
    rw [U.continuousLinearMapAt_symmL hU] at HH
    have HHH:=congrArg C HH
    rw [V.symmL_continuousLinearMapAt hV] at HHH
    exact HHH.symm
  rw [frameNormDet_at hz',frameNormDet_at he]
  change E.toLinearMap.normDet*B.toLinearMap.normDet=C.toLinearMap.normDet*|A.det|
  have h1:=LinearMap.normDet_comp_of_finrank_eq B.toLinearMap E.toLinearMap (show Module.finrank ℝ (Model n)=Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) z.1) by rw [tangent_finrank]; exact finrank_euclideanSpace_fin)
  have h2:=LinearMap.normDet_comp_of_finrank_eq A.toLinearMap C.toLinearMap rfl
  rw [LinearMap.normDet_eq_abs_det] at h2
  change (E.comp B).toLinearMap.normDet=_ at h1
  change (C.comp A).toLinearMap.normDet=_ at h2
  rw [←h1,hEB,h2]

lemma continuous_expJacobian_oai : Continuous (fun z:TangentBundle 𝓘(ℝ,Model n) M=>expJacobian z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro c
  let e:=riemannianExp c.1 c.2
  let s:=fun z:TangentBundle 𝓘(ℝ,Model n) M=>
    (chartFiberInverse c.1 (extChartAt 𝓘(ℝ,Model n) c.1 z.1)).toLinearMap.normDet
  let t:=fun z:TangentBundle 𝓘(ℝ,Model n) M=>
    (chartFiberInverse e (extChartAt 𝓘(ℝ,Model n) e (riemannianExp z.1 z.2))).toLinearMap.normDet
  have hproj:Continuous (fun z:TangentBundle 𝓘(ℝ,Model n) M=>z.1):=
    (Bundle.contMDiff_proj (n:=∞) (IB:=𝓘(ℝ,Model n)) (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)).continuous
  have hE:Continuous (fun z:TangentBundle 𝓘(ℝ,Model n) M=>riemannianExp z.1 z.2):=contMDiff_riemannianExp.continuous
  have hsc:ContinuousAt (fun z:TangentBundle 𝓘(ℝ,Model n) M=>extChartAt 𝓘(ℝ,Model n) c.1 z.1) c:=
    (continuousAt_extChartAt (I:=𝓘(ℝ,Model n)) c.1).comp hproj.continuousAt
  have htc:ContinuousAt (fun z:TangentBundle 𝓘(ℝ,Model n) M=>extChartAt 𝓘(ℝ,Model n) e (riemannianExp z.1 z.2)) c:=
    (continuousAt_extChartAt (I:=𝓘(ℝ,Model n)) e).tendsto.comp hE.continuousAt
  have hs:ContinuousAt s c:= (frameNormDet_continuousAt (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) c.1)).tendsto.comp hsc.tendsto
  have ht:ContinuousAt t c:= (frameNormDet_continuousAt (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) e)).tendsto.comp htc.tendsto
  have hsp:0 < s c:=frameNormDet_pos (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) c.1)
  have Hd:ContinuousAt (fun z=>|(coordinateEndpointVertical c z).det|) c:=
    (ContinuousLinearMap.continuous_det.continuousAt.comp (coordinateEndpointVertical_continuousAt c)).abs
  have H:ContinuousAt (fun z=>t z*|(coordinateEndpointVertical c z).det|/s z) c:=(ht.mul Hd).div hs hsp.ne'
  apply H.congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I:=𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c,
    hE.continuousAt.eventually (extChartAt_source_mem_nhds (I:=𝓘(ℝ,Model n)) e),
    hs.eventually (lt_mem_nhds hsp)] with z hzs hzt hsz
  exact (eq_div_iff hsz.ne').mpr (expJacobian_coordinate_identity c z hzs hzt)
end ExpJacContinuity
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.continuous_expJacobian_oai.{u_1} := @OAI.WeakMTWTransport.continuous_expJacobian_oai.{u_1}
