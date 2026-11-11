-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.exists_maximum_simultaneous
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:46:50.65513+00:00
-- url     : https://prove2.me/submissions/72319d6a-c1a2-4b99-9698-5c27f4df5fbc

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
import Theorems.Thm_OAI_WeakMTWTransport_MaximumDiagonal_center_phase_compact
import Theorems.Thm_OAI_WeakMTWTransport_MaximumJensenFamily_center_regular
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_coordinate_sample_pole_matrix
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_maximum_true_outer
import Theorems.Thm_OAI_WeakMTWTransport_exists_maximum_true_center

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_GraphInverse
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

lemma WeakMTW.graphHomeomorph_inverse_pole (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1) (z:M) :
    ((hmtw.graphHomeomorph hv ht ht1).symm z).1.1=hopfPole (n := n) t (cTransform v) z := by
  let q := (hmtw.graphHomeomorph hv ht ht1).symm z
  have H := congrArg Bundle.TotalSpace.proj (hmtw.hopfLax_backward_flow hv ht ht1 q)
  change hopfPole (n := n) t (cTransform v)
    ((hmtw.graphHomeomorph hv ht ht1) q)=q.1.1 at H
  simpa only [q,Homeomorph.apply_symm_apply] using H.symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinateMatrices
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

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma graphCoordinate_normalSubdifferential {a : M} {u : M → ℝ}
    (q : subgradientGraph (n := n) u)
    (hq : q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    chartFiberInverse a (graphBaseCoordinate a q.1) (graphVelocityCoordinate a q.1)∈
      normalSubdifferential (n := n) u
        ((extChartAt 𝓘(ℝ,Model n) a).symm (graphBaseCoordinate a q.1)) := by
  exact (congrArg (fun z:TangentBundle 𝓘(ℝ,Model n) M=>z.2∈normalSubdifferential u z.1)
    (graph_coordinate_reconstruction hq)).mpr q.2

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MovingHessianLimit
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
variable {Q E F : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma tendsto_clm_apply {ι : Type*} {l : Filter ι}
    {A : ι → E →L[ℝ] F} {v : ι → E} {A₀ : E →L[ℝ] F} {v₀ : E}
    (hA : Tendsto A l (𝓝 A₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i=>A i (v i)) l (𝓝 (A₀ v₀)) := by
  have hc : Continuous (fun q:(E →L[ℝ] F)×E => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  exact (hc.tendsto (A₀,v₀)).comp (hA.prodMk_nhds hv)

lemma bilinear_limit_nonneg {ι : Type*} {l : Filter ι} [NeBot l]
    {B : ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : Tendsto B l (𝓝 B₀)) (hp : ∀ᶠ i in l,∀ d:E,0≤B i d d) (d:E) :
    0≤B₀ d d := by
  exact ge_of_tendsto (tendsto_clm_apply (tendsto_clm_apply hB tendsto_const_nhds) tendsto_const_nhds)
    (hp.mono (fun i hi=>hi d))

lemma bilinear_limit_symm {ι : Type*} {l : Filter ι} [NeBot l]
    {B : ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : Tendsto B l (𝓝 B₀)) (hp : ∀ᶠ i in l,∀ d e:E,B i d e=B i e d) (d e:E) :
    B₀ d e=B₀ e d := by
  exact tendsto_nhds_unique_of_eventuallyEq
    (tendsto_clm_apply (tendsto_clm_apply hB tendsto_const_nhds) tendsto_const_nhds)
    (tendsto_clm_apply (tendsto_clm_apply hB tendsto_const_nhds) tendsto_const_nhds)
    (hp.mono (fun i hi=>hi d e))

lemma bilinear_limit_kernel {ι : Type*} {l : Filter ι} [NeBot l]
    {B : ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ}
    {v : ι → E} {v₀ : E} (hB : Tendsto B l (𝓝 B₀)) (hv : Tendsto v l (𝓝 v₀))
    (hk : ∀ᶠ i in l,∀ d:E,B i (v i) d=0) (d:E) : B₀ v₀ d=0 := by
  exact tendsto_nhds_unique_of_eventuallyEq
    (tendsto_clm_apply (tendsto_clm_apply hB hv) tendsto_const_nhds) tendsto_const_nhds
    (hk.mono (fun i hi=>hi d))
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumRow
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

lemma MaximumRow.graph_inverse {v : M → ℝ} {a D b bplus t : ℝ} {Bc Bo : ℝ → ℝ} {z : M}
    (R : MaximumRow (n := n) v a D b bplus t Bc Bo z)
    (hmtw : WeakMTW (n := n) (M := M)) (hv : Continuous v) (ho : Continuous Bo)
    (ht : 0<t) (ht1 : t<1) :
    (hmtw.graphHomeomorph (continuous_modifiedDatum hv a D b ho) ht ht1).symm z=R.q := by
  apply (hmtw.graphHomeomorph (continuous_modifiedDatum hv a D b ho) ht ht1).injective
  exact (Homeomorph.apply_symm_apply _ _).trans R.projection.symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_MaximumJensen
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

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma MaximumRow.jensen_center_limit {v : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {z c : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    {N : Set (Model n)}
    (J : JensenSamplesAt (modifiedDatum v α D b Bo) (modifiedDatum v α D b Bc) t c z N)
    (hc : z∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    Tendsto (fun k=>extChartAt 𝓘(ℝ,Model n) c (J.Y (J.z k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c (riemannianExp R.q.1.1 R.q.1.2))) := by
  let χ := extChartAt 𝓘(ℝ,Model n) c
  have hdata := J.actual (χ z) J.centerInRegion
  have hval := (hdata.2.2.1 (J.Y (χ z))).mpr rfl
  change hopfLax (1-t) (modifiedDatum v α D b Bc) (χ.symm (χ z))=_ at hval
  rw [χ.left_inv hc] at hval
  have hy : J.Y (χ z)=riemannianExp R.q.1.1 R.q.1.2 := (R.center _).mp hval
  have H := (J.selectorContinuous.continuousAt (J.openRegion.mem_nhds J.centerInRegion)).tendsto.comp J.points
  rwa [hy] at H

end WeakMTWTransport

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

lemma bilinearMatrix_det (B:E →L[ℝ] E →L[ℝ] ℝ) :
    (bilinearMatrix B).det=(bilinearOperator B).det := by
  exact LinearMap.det_toMatrix _ _

lemma bilinearMatrix_quad (B:E →L[ℝ] E →L[ℝ] ℝ)
    (v:Fin (Module.finrank ℝ E) → ℝ) :
    v ⬝ᵥ (bilinearMatrix B *ᵥ v)=
      B ((stdOrthonormalBasis ℝ E).toBasis.equivFun.symm v)
        ((stdOrthonormalBasis ℝ E).toBasis.equivFun.symm v) := by
  let b:=stdOrthonormalBasis ℝ E
  let w:=b.toBasis.equivFun.symm v
  have hv: (fun i=>b.repr w i)=v:=by
    change b.toBasis.equivFun (b.toBasis.equivFun.symm v)=v
    exact b.toBasis.equivFun.apply_symm_apply v
  have hm:bilinearMatrix B *ᵥ v=(fun i=>b.repr (bilinearOperator B w) i):=by
    rw [←hv]
    exact (bilinearOperator B).toLinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis w
  rw [hm]
  nth_rw 1 [←hv]
  have H:=b.repr.inner_map_map (bilinearOperator B w) w
  rw [bilinearOperator_inner] at H
  simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct_comm] using H

end BilinearMatrix
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_DeterminantOrder
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

section DeterminantOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma det_one_add_posSemidef_ge_one {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    1 ≤ (1 + A).det := by
  have hspec := hA.isHermitian.spectral_theorem
  let U := hA.isHermitian.eigenvectorUnitary
  have hconj : (1 + A) =
      Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U
        (Matrix.diagonal (fun i => 1 + hA.isHermitian.eigenvalues i)) := by
    rw [show Matrix.diagonal (fun i => 1 + hA.isHermitian.eigenvalues i) =
      1 + Matrix.diagonal hA.isHermitian.eigenvalues by
        rw [← Matrix.diagonal_one, ← Matrix.diagonal_add]]
    simp only [map_add, map_one]
    congr 1
  rw [hconj, Unitary.conjStarAlgAut_apply]
  have hu : (U : Matrix n n ℝ) * star (U : Matrix n n ℝ) = 1 := by
    exact Unitary.coe_mul_star_self U
  have hdetu : (U : Matrix n n ℝ).det * (star (U : Matrix n n ℝ)).det = 1 := by
    rw [← Matrix.det_mul, hu, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, hdetu, one_mul,
    Matrix.det_diagonal]
  exact Finset.one_le_prod (fun eigenIndex _ => by
    linarith [hA.eigenvalues_nonneg eigenIndex])

lemma det_le_of_posDef_le {A B : Matrix n n ℝ} (hA : A.PosDef) (hAB : A ≤ B) :
    A.det ≤ B.det := by
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  have hRdet : R.det ≠ 0 := by
    have heq : A.det = R.det * R.det := by
      rw [hR, Matrix.det_mul]
      simp only [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, star_trivial]
    intro hz
    rw [hz, zero_mul] at heq
    exact hA.det_pos.ne' heq
  have hRi : IsUnit R.det := isUnit_iff_ne_zero.mpr hRdet
  let S := R⁻¹
  have hrs : R * S = 1 := R.mul_nonsing_inv hRi
  have hnorm : star S * A * S = 1 := by
    rw [hR]
    calc
      star S * (star R * R) * S = star (R * S) * (R * S) := by
        simp only [star_mul]; noncomm_ring
      _ = 1 := by rw [hrs]; simp
  have hD : (star S * (B - A) * S).PosSemidef :=
    hAB.conjTranspose_mul_mul_same S
  have hbound := det_one_add_posSemidef_ge_one hD
  have heq : 1 + star S * (B - A) * S = star S * B * S := by
    rw [← hnorm]
    noncomm_ring
  rw [heq] at hbound
  have hanorm := congrArg Matrix.det hnorm
  simp only [Matrix.det_mul, Matrix.star_eq_conjTranspose,
    Matrix.det_conjTranspose, star_trivial, Matrix.det_one] at hanorm hbound
  nlinarith [hA.det_pos]

lemma det_one_add_vecMulVec (u v : n → ℝ) :
    (1 + Matrix.vecMulVec u v).det = 1 + v ⬝ᵥ u := by
  have heq : Matrix.vecMulVec u v =
      Matrix.replicateCol Unit u * Matrix.replicateRow Unit v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  rw [heq, Matrix.det_one_add_replicateCol_mul_replicateRow]

omit [DecidableEq n] in
lemma congruence_rank_one (S : Matrix n n ℝ) (p : n → ℝ) :
    Sᵀ * Matrix.vecMulVec p p * S =
      Matrix.vecMulVec (Sᵀ *ᵥ p) (Sᵀ *ᵥ p) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_transpose S p]

lemma oblique_fixes_kernel_form {L : Matrix n n ℝ} (hL : L.IsHermitian)
    {e : n → ℝ} (he : L *ᵥ e = 0) (a : n → ℝ) :
    (1 + Matrix.vecMulVec e a)ᵀ * L * (1 + Matrix.vecMulVec e a) = L := by
  have htr : Lᵀ = L := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hL.eq
  have hleft : (1 + Matrix.vecMulVec e a)ᵀ * L = L := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_vecMulVec,
      Matrix.add_mul, Matrix.one_mul, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose,
      htr, he, Matrix.vecMulVec_zero, add_zero]
  rw [hleft, Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, he,
    Matrix.zero_vecMulVec, add_zero]

omit [DecidableEq n] in

lemma transpose_congruence_mono {A B : Matrix n n ℝ} (hAB : A ≤ B)
    (S : Matrix n n ℝ) : Sᵀ * A * S ≤ Sᵀ * B * S := by
  have h := hAB.conjTranspose_mul_mul_same S
  rw [Matrix.le_iff]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul] using h
end DeterminantOrder

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FunctionalDet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Matrix
open scoped MatrixOrder

namespace WeakMTWTransport
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma determinant_gain_of_functional_bounds [Nonempty n]
    {L V W : Matrix n n ℝ} {e p pi : n → ℝ} {m beta gamma : ℝ}
    (hL : L.IsHermitian) (he : L *ᵥ e = 0)
    (hq : 0 < p ⬝ᵥ e) (hqi : p ⬝ᵥ e ≤ pi ⬝ᵥ e)
    (hm : 0 < m) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hV : V.PosDef) (hVL : V ≤ L + beta • Matrix.vecMulVec p p)
    (hLW : m • L + gamma • Matrix.vecMulVec pi pi ≤ W) :
    gamma * m ^ (Fintype.card n - 1) * V.det ≤ beta * W.det := by
  let q := p ⬝ᵥ e
  let qi := pi ⬝ᵥ e
  let t := Real.sqrt (gamma / (m * beta))
  have hq0 : q ≠ 0 := ne_of_gt hq
  have ht : 0 < t := Real.sqrt_pos.2 (div_pos hgamma (mul_pos hm hbeta))
  have ht2 : t ^ 2 = gamma / (m * beta) :=
    Real.sq_sqrt (le_of_lt (div_pos hgamma (mul_pos hm hbeta)))
  let a : n → ℝ := q⁻¹ • (t • pi - p)
  let S : Matrix n n ℝ := 1 + Matrix.vecMulVec e a
  have hSp : Sᵀ *ᵥ p = t • pi := by
    dsimp [S]
    rw [Matrix.mulVec_transpose, Matrix.vecMul_add, Matrix.vecMul_one,
      Matrix.vecMul_vecMulVec]
    change p + q • (q⁻¹ • (t • pi - p)) = t • pi
    rw [smul_smul, mul_inv_cancel₀ hq0, one_smul, add_sub_cancel]
  have hSdet : S.det = t * qi / q := by
    dsimp [S]
    rw [det_one_add_vecMulVec]
    dsimp [a]
    rw [smul_dotProduct, sub_dotProduct, smul_dotProduct]
    change 1 + q⁻¹ * (t * qi - q) = t * qi / q
    field_simp
    ring
  have hSge : t ≤ S.det := by
    rw [hSdet, le_div_iff₀ hq]
    exact mul_le_mul_of_nonneg_left hqi ht.le
  have hSpos : 0 < S.det := ht.trans_le hSge
  have hSinj : Function.Injective S.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det S).2 (isUnit_iff_ne_zero.2 hSpos.ne'))
  have hsmall : (m • (Sᵀ * V * S)).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hV.conjTranspose_mul_mul_same hSinj).smul hm
  have hfix : Sᵀ * L * S = L := oblique_fixes_kernel_form hL he a
  have hscalar : m * beta * t ^ 2 = gamma := by
    rw [ht2]
    field_simp
  have heq : m • (Sᵀ * (L + beta • Matrix.vecMulVec p p) * S) =
      m • L + gamma • Matrix.vecMulVec pi pi := by
    rw [Matrix.mul_add Sᵀ L (beta • Matrix.vecMulVec p p), Matrix.add_mul, hfix, smul_add,
      Matrix.mul_smul, Matrix.smul_mul, congruence_rank_one, hSp]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.vecMulVec_apply, Pi.smul_apply]
    linear_combination pi i * pi j * hscalar
  have horder : m • (Sᵀ * V * S) ≤ W := by
    apply le_trans _ hLW
    rw [← heq]
    have h := (transpose_congruence_mono hVL S).smul hm.le
    rw [Matrix.le_iff]
    simpa only [smul_sub] using h
  have hdet := det_le_of_posDef_le hsmall horder
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  have hsquare : t ^ 2 ≤ S.det ^ 2 := by nlinarith
  have hmpow : 0 < m ^ Fintype.card n := pow_pos hm _
  have hlower : m ^ Fintype.card n * t ^ 2 * V.det ≤ W.det := by
    nlinarith [mul_nonneg (mul_nonneg hmpow.le (sub_nonneg.2 hsquare)) hV.det_pos.le]
  have hcard : Fintype.card n = (Fintype.card n - 1) + 1 :=
    (Nat.sub_add_cancel Fintype.card_pos).symm
  have hpower : m ^ Fintype.card n = m ^ (Fintype.card n - 1) * m := by
    conv_lhs => rw [hcard, pow_succ]
  have hcancel : beta * (m ^ Fintype.card n * t ^ 2 * V.det) =
      gamma * m ^ (Fintype.card n - 1) * V.det := by
    rw [hpower]
    calc
      beta * (m ^ (Fintype.card n - 1) * m * t ^ 2 * V.det) =
          m ^ (Fintype.card n - 1) * V.det * (m * beta * t ^ 2) := by ring
      _ = gamma * m ^ (Fintype.card n - 1) * V.det := by rw [hscalar]; ring
  rw [← hcancel]
  exact mul_le_mul_of_nonneg_left hlower hbeta.le

end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearDet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Matrix
open scoped MatrixOrder

namespace WeakMTWTransport
section BilinearDet
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma bilinearMatrix_apply (B:E →L[ℝ] E →L[ℝ] ℝ) (i j:Fin (Module.finrank ℝ E)) :
    bilinearMatrix B i j=B (stdOrthonormalBasis ℝ E j) (stdOrthonormalBasis ℝ E i) := by
  simp only [bilinearMatrix,LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis,OrthonormalBasis.repr_apply_apply]
  change inner ℝ (stdOrthonormalBasis ℝ E i) (bilinearOperator B (stdOrthonormalBasis ℝ E j)) = _
  rw [real_inner_comm,bilinearOperator_inner]

lemma functional_coords_dot (f:E →L[ℝ] ℝ) (d:E) :
    (fun i=>f (stdOrthonormalBasis ℝ E i)) ⬝ᵥ (stdOrthonormalBasis ℝ E).toBasis.equivFun d=f d := by
  have H:=congrArg f ((stdOrthonormalBasis ℝ E).toBasis.sum_repr d)
  simpa only [map_sum,map_smul,smul_eq_mul,mul_comm,dotProduct,OrthonormalBasis.coe_toBasis,
    Module.Basis.equivFun_apply] using H

lemma bilinearMatrix_symmetric {B:E →L[ℝ] E →L[ℝ] ℝ} (hs:∀d e,B d e=B e d) :
    (bilinearMatrix B).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,bilinearMatrix_apply,hs]

lemma bilinearMatrix_positive {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hs:∀d e,B d e=B e d) (hp:∀d,d≠0 → 0 < B d d) :
    (bilinearMatrix B).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨bilinearMatrix_symmetric hs,?_⟩
  intro v hv
  simp only [star_trivial,bilinearMatrix_quad]
  apply hp
  intro H
  apply hv
  exact (stdOrthonormalBasis ℝ E).toBasis.equivFun.symm.injective (by simpa only [map_zero] using H)

lemma bilinearMatrix_le {A B:E →L[ℝ] E →L[ℝ] ℝ}
    (ha:∀d e,A d e=A e d) (hb:∀d e,B d e=B e d)
    (h:∀d,A d d≤B d d) : bilinearMatrix A≤bilinearMatrix B := by
  rw [Matrix.le_iff]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨(bilinearMatrix_symmetric hb).sub
    (bilinearMatrix_symmetric ha),?_⟩
  intro d
  simpa only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,bilinearMatrix_quad,sub_nonneg] using
    h ((stdOrthonormalBasis ℝ E).toBasis.equivFun.symm d)

lemma bilinearMatrix_rank_add (L:E →L[ℝ] E →L[ℝ] ℝ) (f:E →L[ℝ] ℝ) (m β:ℝ) :
    bilinearMatrix (m • L+β • f.smulRight f)=m • bilinearMatrix L+
      β • Matrix.vecMulVec (fun i=>f (stdOrthonormalBasis ℝ E i)) (fun i=>f (stdOrthonormalBasis ℝ E i)) := by
  ext i j
  simp only [bilinearMatrix_apply,_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply]
  ring

lemma bilinear_determinant_gain [Nontrivial E]
    {L V W:E →L[ℝ] E →L[ℝ] ℝ} {f g:E →L[ℝ] ℝ} {e:E} {m β γ:ℝ}
    (hLs:∀d e,L d e=L e d) (hVs:∀d e,V d e=V e d) (hWs:∀d e,W d e=W e d)
    (hker:∀d,L e d=0) (hf:0 < f e) (hg:f e≤g e)
    (hm:0 < m) (hβ:0 < β) (hγ:0 < γ) (hV:∀d,d≠0 → 0 < V d d)
    (hVL:∀d,V d d≤L d d+β*(f d)^2)
    (hLW:∀d,m*L d d+γ*(g d)^2≤W d d) :
    γ*m^(Module.finrank ℝ E-1)*(bilinearOperator V).det≤β*(bilinearOperator W).det := by
  classical
  let b:=(stdOrthonormalBasis ℝ E).toBasis
  let : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp (Module.finrank_pos (R:=ℝ))
  have hLe:bilinearOperator L e=0:=by
    apply ext_inner_right ℝ
    intro d
    simp only [bilinearOperator_inner,hker,inner_zero_left]
  have hMe:bilinearMatrix L *ᵥ b.equivFun e=0:=by
    change (bilinearOperator L).toLinearMap.toMatrix b b *ᵥ b.equivFun e=0
    rw [Module.Basis.equivFun_apply,(bilinearOperator L).toLinearMap.toMatrix_mulVec_repr b b e]
    change (fun i => b.repr (bilinearOperator L e) i) = 0
    rw [hLe,map_zero]
    rfl
  have hfl:=functional_coords_dot f e
  have hgl:=functional_coords_dot g e
  have hF:∀d e,(L+β • f.smulRight f) d e=(L+β • f.smulRight f) e d:=by
    intro d e
    simp only [_root_.add_apply,_root_.smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul,hLs]
    ring
  have hG:∀d e,(m • L+γ • g.smulRight g) d e=(m • L+γ • g.smulRight g) e d:=by
    intro d e
    simp only [_root_.add_apply,_root_.smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul,hLs]
    ring
  have hVL':bilinearMatrix V≤bilinearMatrix L+β • Matrix.vecMulVec
      (fun i=>f (stdOrthonormalBasis ℝ E i)) (fun i=>f (stdOrthonormalBasis ℝ E i)):=by
    have H:=bilinearMatrix_le hVs hF (fun d=>by
      simpa only [_root_.add_apply,_root_.smul_apply,
        ContinuousLinearMap.smulRight_apply,smul_eq_mul,pow_two] using hVL d)
    have hr:=bilinearMatrix_rank_add L f 1 β
    simp only [one_smul] at hr
    rwa [hr] at H
  have hLW':m • bilinearMatrix L+γ • Matrix.vecMulVec
      (fun i=>g (stdOrthonormalBasis ℝ E i)) (fun i=>g (stdOrthonormalBasis ℝ E i))≤bilinearMatrix W:=by
    rw [←bilinearMatrix_rank_add]
    apply bilinearMatrix_le hG hWs
    intro d
    simpa only [_root_.add_apply,_root_.smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul,pow_two] using hLW d
  have H:=determinant_gain_of_functional_bounds (bilinearMatrix_symmetric hLs) hMe
    (by rwa [hfl]) (by rwa [hfl,hgl]) hm hβ hγ (bilinearMatrix_positive hVs hV) hVL' hLW'
  simpa only [Fintype.card_fin,bilinearMatrix_det] using H
end BilinearDet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_FunctionalCoercive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section FunctionalCoercive
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma functional_rank_one_positive
    {L V:E →L[ℝ] E →L[ℝ] ℝ} {f g:E →L[ℝ] ℝ} {e:E} {β m γ:ℝ}
    (hLs:∀d e,L d e=L e d) (hL:∀d,0 ≤ L d d)
    (hV:∀d,d≠0 → 0 < V d d)
    (hVL:∀d,V d d ≤ L d d+β*(f d)^2)
    (hker:∀d,L e d=0) (hf:f e≠0) (hg:g e≠0)
    (hm:0 < m) (hγ:0 < γ) :
    ∀d:E,d≠0 → 0 < m*L d d+γ*(g d)^2 := by
  intro d hd
  have hnon:0 ≤ m*L d d+γ*(g d)^2:=
    add_nonneg (mul_nonneg hm.le (hL d)) (mul_nonneg hγ.le (sq_nonneg _))
  by_contra H
  have hz:m*L d d+γ*(g d)^2=0:=le_antisymm (not_lt.mp H) hnon
  have hLd:L d d=0:=by
    have :m*L d d=0:=by nlinarith only [hz,mul_nonneg hm.le (hL d),mul_nonneg hγ.le (sq_nonneg (g d))]
    exact (mul_eq_zero.mp this).resolve_left hm.ne'
  have hgd:g d=0:=by
    have :γ*(g d)^2=0:=by rw [hLd,mul_zero,zero_add] at hz; exact hz
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp this).resolve_left hγ.ne')
  let a:=f d/f e
  let w:=d-a • e
  have hfw:f w=0:=by
    dsimp only [w,a]
    rw [map_sub,map_smul,smul_eq_mul,div_mul_cancel₀ _ hf,sub_self]
  have hLw:L w w=0:=by
    dsimp only [w]
    simp only [map_sub,map_smul,sub_apply,smul_apply,
      smul_eq_mul,hker,hLs d e,hLd,mul_zero,sub_zero]
  have hw:w=0:=by
    by_contra hw
    have H:=hVL w
    rw [hfw,hLw,pow_two,mul_zero,mul_zero,add_zero] at H
    exact (not_lt_of_ge H) (hV w hw)
  have hdw:d=a • e:=sub_eq_zero.mp hw
  have ha:a=0:=by
    rw [hdw,map_smul,smul_eq_mul] at hgd
    exact (mul_eq_zero.mp hgd).resolve_right hg
  exact hd (by rw [hdw,ha,zero_smul])
end FunctionalCoercive
end WeakMTWTransport

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumSample
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

lemma MaximumRow.jensen_graph_limit {v : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {z a c : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    (hmtw : WeakMTW (n := n) (M := M)) (hv : Continuous v) (ho : Continuous Bo)
    (ht : 0<t) (ht1 : t<1) {N : Set (Model n)}
    (J : JensenSamplesAt (modifiedDatum v α D b Bo) (modifiedDatum v α D b Bc) t c z N)
    (hc : z∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (ha : R.q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let χ := extChartAt 𝓘(ℝ,Model n) c
    let e := hmtw.graphHomeomorph (continuous_modifiedDatum hv α D b ho) ht ht1
    let q := fun j=>e.symm (χ.symm (J.z j))
    Tendsto (fun j=>(q j).1) atTop (𝓝 R.q.1) ∧
      Tendsto (fun j=>graphBaseCoordinate a (q j).1) atTop (𝓝 (graphBaseCoordinate a R.q.1)) ∧
      Tendsto (fun j=>graphVelocityCoordinate a (q j).1) atTop (𝓝 (graphVelocityCoordinate a R.q.1)) := by
  dsimp only
  let χ := extChartAt 𝓘(ℝ,Model n) c
  let e := hmtw.graphHomeomorph (continuous_modifiedDatum hv α D b ho) ht ht1
  let q := fun j=>e.symm (χ.symm (J.z j))
  have HC := (continuousAt_extChartAt_symm'' (χ.map_source hc)).tendsto.comp J.points
  rw [χ.left_inv hc] at HC
  have H := (e.symm.continuous.tendsto z).comp HC
  rw [R.graph_inverse hmtw hv ho ht ht1] at H
  have Hq := continuous_subtype_val.tendsto R.q |>.comp H
  let χa := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hs : R.q.1∈χa.source := (tangent_chart_source_iff _ _).mpr ha
  have Hchart := ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds hs)).tendsto.comp Hq
  exact ⟨Hq,Hchart.fst_nhds,Hchart.snd_nhds⟩

lemma MaximumRow.jensen_approximation {v : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {z a c : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    (hmtw : WeakMTW (n := n) (M := M)) (hv : Continuous v) (ho : Continuous Bo)
    (ht : 0<t) (ht1 : t<1) {N : Set (Model n)}
    (J : JensenSamplesAt (modifiedDatum v α D b Bo) (modifiedDatum v α D b Bc) t c z N)
    (hc : z∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (ha : R.q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let χ := extChartAt 𝓘(ℝ,Model n) c
    let e := hmtw.graphHomeomorph (continuous_modifiedDatum hv α D b ho) ht ht1
    let q := fun j=>e.symm (χ.symm (J.z j))
    ∀ P:ChartFixedPrefixLimit a (modifiedDatum v α D b Bo)
      (hopfLax (1-t) (modifiedDatum v α D b Bc)) t q R.q,
    ∀ ε:ℝ,0<ε → ∀ W:ℕ → Prop,(∀ᶠ j in atTop,W j) →
    ∃ j:ℕ,
      (q (P.σ j)).1.1∈(extChartAt 𝓘(ℝ,Model n) a).source ∧
      J.z (P.σ j)∈χ.target ∧
      dist (graphBaseCoordinate a (q (P.σ j)).1) (graphBaseCoordinate a R.q.1)<ε ∧
      dist (graphVelocityCoordinate a (q (P.σ j)).1) (graphVelocityCoordinate a R.q.1)<ε ∧
      dist (χ (J.Y (J.z (P.σ j)))) (χ (riemannianExp R.q.1.1 R.q.1.2))<ε ∧
      ‖fderiv ℝ (chartOuterEnvelope (modifiedDatum v α D b Bo) t c) (J.z (P.σ j))+
        fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D b Bc) t c) (J.z (P.σ j))‖<ε ∧
      ‖coordinateCenterMatrix a t (hopfLax (1-t) (modifiedDatum v α D b Bc))
        (graphBaseCoordinate a (q (P.σ j)).1) (graphVelocityCoordinate a (q (P.σ j)).1)-P.H‖<ε ∧
      ‖coordinatePoleMatrix a t (modifiedDatum v α D b Bo)
        (graphBaseCoordinate a (q (P.σ j)).1) (graphVelocityCoordinate a (q (P.σ j)).1)-P.L‖<ε ∧
      dist (P.pj j) P.pj₀<ε ∧ dist (P.w j) P.w₀<ε ∧ W j := by
  dsimp only
  intro P ε hε W hW
  let : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
  obtain ⟨Hq,Hb,Hp⟩ := R.jensen_graph_limit hmtw hv ho ht ht1 J hc ha
  have hσ := P.strictMono.tendsto_atTop
  have Hbase := (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).tendsto R.q.1
    |>.comp (Hq.comp hσ)
  have Ha := Hbase.eventually ((isOpen_extChartAt_source _).mem_nhds ha)
  have Ht := (J.points.comp hσ).eventually ((isOpen_extChartAt_target _).mem_nhds
    ((extChartAt 𝓘(ℝ,Model n) c).map_source hc))
  have HB := (Hb.comp hσ).eventually (Metric.ball_mem_nhds _ hε)
  have HP := (Hp.comp hσ).eventually (Metric.ball_mem_nhds _ hε)
  have HY := ((R.jensen_center_limit J hc).comp hσ).eventually (Metric.ball_mem_nhds _ hε)
  have HG := (J.gradients.comp hσ).eventually (Metric.ball_mem_nhds _ hε)
  have HH := P.HLimit.eventually (Metric.ball_mem_nhds P.H hε)
  have HL := P.LLimit.eventually (Metric.ball_mem_nhds P.L hε)
  have Hi := P.pjLimit.eventually (Metric.ball_mem_nhds _ hε)
  have Hw := P.wLimit.eventually (Metric.ball_mem_nhds _ hε)
  have Hall := Ha.and (Ht.and (HB.and (HP.and (HY.and (HG.and (HH.and (HL.and (Hi.and (Hw.and hW)))))))))
  obtain ⟨j,hj⟩ := Hall.exists
  exact ⟨j,hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,
    by simpa only [Metric.mem_ball,Function.comp_apply,dist_zero_right] using hj.2.2.2.2.2.1,
    by simpa only [Metric.mem_ball,Function.comp_apply,dist_eq_norm] using hj.2.2.2.2.2.2.1,
    by simpa only [Metric.mem_ball,Function.comp_apply,dist_eq_norm] using hj.2.2.2.2.2.2.2.1,
    hj.2.2.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2.2.2.1,hj.2.2.2.2.2.2.2.2.2.2⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumDiagonal
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
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumJensenFamily.exists_diagonal (J : MaximumJensenFamily hmtw hv ho F a c N)
    {ε : ℕ → ℝ} (hε : ∀ k,0<ε k) {P : ℕ → ℕ → Prop}
    (hP : ∀ k,∀ᶠ j in atTop,P k j) : Nonempty (MaximumDiagonal J ε P) := by
  have H (k:ℕ) := (F.row k).jensen_approximation hmtw hv ho (F.prefixTime k).1
    (F.prefixTime k).2 (J.sample k) (J.endpointSource k) (J.poleSource k) (J.first k)
    (ε k) (hε k) (P k) (hP k)
  choose ν hs hc hb hp hy hg hH hL hi hw hex using H
  exact ⟨⟨ν,hs,hc,hb,hp,hy,hg,hH,hL,hi,hw,hex⟩⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MaximumPolePositive
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
section MaximumPolePositive
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumJensenFamily.sample_pole_positive (J:MaximumJensenFamily hmtw hv ho F a c N)
    (k:ℕ) : ∀ᶠ j in atTop,∀d:Model n,0 ≤ J.sampleL k j d d := by
  let χ:=extChartAt 𝓘(ℝ,Model n) c
  let v0:=modifiedDatum v α D (F.b k) Bo
  have hv0:=continuous_modifiedDatum hv α D (F.b k) ho
  have ht:=(F.prefixTime k).1
  have ht1:=(F.prefixTime k).2
  have hσ:=(J.first k).strictMono.tendsto_atTop
  obtain ⟨hQ,hb,hp⟩:=(F.row k).jensen_graph_limit hmtw hv ho ht ht1
    (J.sample k) (J.endpointSource k) (J.poleSource k)
  have hbase: Tendsto (fun j=>(J.samplePoint k j).1.1) atTop (𝓝 (F.row k).q.1.1) :=
    (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).tendsto (F.row k).q.1
      |>.comp (hQ.comp hσ)
  have ha:=hbase.eventually ((isOpen_extChartAt_source _).mem_nhds (J.poleSource k))
  have hd:=hbase.eventually ((isOpen_extChartAt_source (F.row k).q.1.1).mem_nhds
    (mem_extChartAt_source (I := 𝓘(ℝ,Model n)) (F.row k).q.1.1))
  have hz:=((J.sample k).points.comp hσ).eventually ((isOpen_extChartAt_target c).mem_nhds
    (χ.map_source (J.endpointSource k)))
  have hpole:chartActualPole v0 (F.t k) c (χ (F.z k))=(F.row k).q.1.1 := by
    dsimp only [chartActualPole]
    rw [χ.left_inv (J.endpointSource k)]
    rw [←hmtw.graphHomeomorph_inverse_pole hv0 ht ht1 (F.z k)]
    exact congrArg (fun q=>q.1.1) ((F.row k).graph_inverse hmtw hv ho ht ht1)
  filter_upwards [ha,hd,hz] with j haj hdj hzj
  let q:=J.samplePoint k j
  let b:=graphBaseCoordinate a q.1
  let p:=graphVelocityCoordinate a q.1
  have hbt:b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source haj
  have he:movingPrefix a (F.t k) b p=graphProjection (cTransform v0) (F.t k) q :=
    movingPrefix_graph_coordinates haj (F.t k)
  have hec:χ (movingPrefix a (F.t k) b p)=(J.sample k).z (J.sampleIndex k j) := by
    rw [he,J.sampleProjection]
    exact χ.right_inv hzj
  have hs:movingPrefix a (F.t k) b p∈χ.source := by
    rw [he,J.sampleProjection]
    exact χ.map_target hzj
  have hbd:(extChartAt 𝓘(ℝ,Model n) a).symm b∈
      (extChartAt 𝓘(ℝ,Model n) (F.row k).q.1.1).source := by
    change (extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a q.1.1)∈_
    rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv haj]
    exact hdj
  have hD: DifferentiableAt ℝ (fun w:Model n=>extChartAt 𝓘(ℝ,Model n) (F.row k).q.1.1
      (hopfPole (n := n) (F.t k) (cTransform v0) (χ.symm w)))
      (χ (movingPrefix a (F.t k) b p)) := by
    rw [hec,←hpole]
    exact ((J.sample k).samples (J.sampleIndex k j)).2.2.2.2.2.1.differentiableAt
  exact (hmtw.coordinate_sample_pole_matrix hv0 ht ht1 hbt
    (graphCoordinate_normalSubdifferential q haj) hs hbd hD).1

end MaximumPolePositive
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_ModelTangentJet
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
section ModelTangentJet
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
lemma center_frame_identity (a : M) (d : Model n) :
    (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ a d=d := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) a)]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source a)

end ModelTangentJet
end WeakMTWTransport

end
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
lemma frameMetric_center (a:M) (d e:Model n) :
    frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d e=
      inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from d) e := by
  rw [frameMetric_apply ((extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a))]
  have ha := (extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)
  dsimp only [chartFiberInverse]
  rw [ha,center_frame_identity,center_frame_identity]

end FrameMetric
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumPoleSymmetric
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
section MaximumPoleSymmetric
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumJensenFamily.sample_pole_symmetric (J:MaximumJensenFamily hmtw hv ho F a c N)
    (k:ℕ) : ∀ᶠ j in atTop,∀d e:Model n,J.sampleL k j d e=J.sampleL k j e d := by
  let χ:=extChartAt 𝓘(ℝ,Model n) c
  let v0:=modifiedDatum v α D (F.b k) Bo
  have hv0:=continuous_modifiedDatum hv α D (F.b k) ho
  have ht:=(F.prefixTime k).1
  have ht1:=(F.prefixTime k).2
  have hσ:=(J.first k).strictMono.tendsto_atTop
  obtain ⟨hQ,hb,hp⟩:=(F.row k).jensen_graph_limit hmtw hv ho ht ht1
    (J.sample k) (J.endpointSource k) (J.poleSource k)
  have hbase: Tendsto (fun j=>(J.samplePoint k j).1.1) atTop (𝓝 (F.row k).q.1.1) :=
    (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).tendsto (F.row k).q.1
      |>.comp (hQ.comp hσ)
  have ha:=hbase.eventually ((isOpen_extChartAt_source _).mem_nhds (J.poleSource k))
  have hd:=hbase.eventually ((isOpen_extChartAt_source (F.row k).q.1.1).mem_nhds
    (mem_extChartAt_source (I := 𝓘(ℝ,Model n)) (F.row k).q.1.1))
  have hz:=((J.sample k).points.comp hσ).eventually ((isOpen_extChartAt_target c).mem_nhds
    (χ.map_source (J.endpointSource k)))
  have hpole:chartActualPole v0 (F.t k) c (χ (F.z k))=(F.row k).q.1.1 := by
    dsimp only [chartActualPole]
    rw [χ.left_inv (J.endpointSource k)]
    rw [←hmtw.graphHomeomorph_inverse_pole hv0 ht ht1 (F.z k)]
    exact congrArg (fun q=>q.1.1) ((F.row k).graph_inverse hmtw hv ho ht ht1)
  filter_upwards [ha,hd,hz] with j haj hdj hzj
  let q:=J.samplePoint k j
  let b:=graphBaseCoordinate a q.1
  let p:=graphVelocityCoordinate a q.1
  have hbt:b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source haj
  have he:movingPrefix a (F.t k) b p=graphProjection (cTransform v0) (F.t k) q :=
    movingPrefix_graph_coordinates haj (F.t k)
  have hec:χ (movingPrefix a (F.t k) b p)=(J.sample k).z (J.sampleIndex k j) := by
    rw [he,J.sampleProjection]
    exact χ.right_inv hzj
  have hs:movingPrefix a (F.t k) b p∈χ.source := by
    rw [he,J.sampleProjection]
    exact χ.map_target hzj
  have hbd:(extChartAt 𝓘(ℝ,Model n) a).symm b∈
      (extChartAt 𝓘(ℝ,Model n) (F.row k).q.1.1).source := by
    change (extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a q.1.1)∈_
    rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv haj]
    exact hdj
  have hD: DifferentiableAt ℝ (fun w:Model n=>extChartAt 𝓘(ℝ,Model n) (F.row k).q.1.1
      (hopfPole (n := n) (F.t k) (cTransform v0) (χ.symm w)))
      (χ (movingPrefix a (F.t k) b p)) := by
    rw [hec,←hpole]
    exact ((J.sample k).samples (J.sampleIndex k j)).2.2.2.2.2.1.differentiableAt
  exact (hmtw.coordinate_sample_pole_matrix hv0 ht ht1 hbt
    (graphCoordinate_normalSubdifferential q haj) hs hbd hD).2.1

end MaximumPoleSymmetric
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumOuterSamples
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
section MaximumOuterSamples
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumJensenFamily.outer_samples_eventually (J:MaximumJensenFamily hmtw hv ho F a c N)
    (k:ℕ):∀ᶠ j in atTop,J.OuterSampleGood k j := by
  filter_upwards [J.sample_pole_symmetric k,J.sample_pole_positive k,(J.first k).samples]
    with j hs hp hj
  exact ⟨hs,hp,hj.1,hj.2.2.2.1,hj.2.2.2.2⟩

lemma MaximumJensenFamily.exists_outer_diagonal (J:MaximumJensenFamily hmtw hv ho F a c N)
    {ε:ℕ → ℝ} (hε:∀k,0 < ε k):
    Nonempty (MaximumDiagonal J ε J.OuterSampleGood) :=
  J.exists_diagonal hε J.outer_samples_eventually

end MaximumOuterSamples
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumPoleCompact
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
section MaximumPoleCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

local instance poleCompactDualGroup_rb80ebb_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance poleCompactDualSpace_rb80ebb_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance poleCompactBilinearGroup_rb80ebb_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance poleCompactBilinearSpace_rb80ebb_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma MaximumJensenFamily.pole_limit_properties (J:MaximumJensenFamily hmtw hv ho F a c N)
    {L:Model n →L[ℝ] Model n →L[ℝ] ℝ} {q:Model n}
    {r:Fin (Module.finrank ℝ (Model n)+1) → Model n}
    (hL:Tendsto (fun k=>(J.first k).L) atTop (𝓝 L))
    (hp:Tendsto (fun k=>graphVelocityCoordinate a (F.row k).q.1) atTop (𝓝 q))
    (hr:Tendsto (fun k=>(J.first k).pj₀) atTop (𝓝 r)) :
    (∀d,0 ≤ L d d) ∧ (∀d e,L d e=L e d) ∧ (∀i d,L (r i-q) d=0) := by
  refine ⟨bilinear_limit_nonneg hL (Eventually.of_forall (fun k=>(J.first k).positive)),
    bilinear_limit_symm hL (Eventually.of_forall (fun k=>(J.first k).symmetric)),?_⟩
  intro i d
  exact bilinear_limit_kernel hL ((tendsto_pi_nhds.mp hr i).sub hp)
    (Eventually.of_forall (fun k=>(J.first k).kernel i)) d
end MaximumPoleCompact
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumSimultaneous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section MaximumSimultaneous
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance simulDualGroup_rb80ebb_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance simulDualSpace_rb80ebb_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance simulBilinearGroup_rb80ebb_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance simulBilinearSpace_rb80ebb_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma WeakMTW.exists_maximum_simultaneous_oai
    (hmtw:WeakMTW (n:=n) (M:=M)) (hn:0 < n) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃δ:ℝ,δ>0 ∧ ∃K:ℝ,K>0 ∧ ∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),uv∈densityDualClass (metricVolume n) lam cap x0 →
    ∀Lv:ℝ≥0,LipschitzWith Lv (uv.2:M → ℝ) → IsCostDualPair (uv.1:M → ℝ) uv.2 →
    ∀(α D bminus bplus A₀ B₀:ℝ) (Bc Bo:ℝ → ℝ),
    ∀ho:Continuous Bo,ContDiff ℝ ∞ Bc → ContDiff ℝ ∞ Bo →
    (∀b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s))) →
    (∀b∈Icc bminus bplus,StrictMono (fun s=>modifiedScalar α D Bo (b,s))) →
    (∀y,uv.2 y∈Icc A₀ B₀) →
    (∀b∈Icc bminus bplus,∀y:M,0 < deriv (fun s=>modifiedScalar α D Bc (b,s)) (uv.2 y) ∧
      deriv (fun s=>modifiedScalar α D Bc (b,s)) (uv.2 y)<1) →
    ∀Klip:ℝ≥0,(∀b∈Icc bminus bplus,LipschitzWith Klip (modifiedDatum uv.2 α D b Bc)) →
    ∀F:MaximumFamily (n:=n) uv.2 α D bminus bplus Bc Bo,
    ∀(a c:M) (χ:ℝ) (N:Set (Model n)) (r₀:ℝ),0 < χ → 0 < r₀ →
    (∀z∈ball (extChartAt 𝓘(ℝ,Model n) c c) r₀,z∉N →
      OriginalCenterGood (n:=n) uv.1 χ ((extChartAt 𝓘(ℝ,Model n) c).symm z) ∧
      ∃p:Model n,∃A:Model n →L[ℝ] Model n,
        (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
        HasQuadraticExpansion (fun h=>uv.2 ((extChartAt 𝓘(ℝ,Model n) c).symm (z+h))) p A) →
    ∀J:MaximumJensenFamily hmtw uv.2.continuous ho F a c N,
    ∀(q:Model n) (β l κc:ℝ),
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a → riemannianExp a q=c →
    Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto F.b atTop (𝓝 β) → deriv (fun s=>modifiedScalar α D Bc (β,s)) (uv.2 c)=l →
    iteratedDeriv 2 (fun s=>modifiedScalar α D Bc (β,s)) (uv.2 c)=κc →
    l∈U → 0 < l → l<1 → κc<0 →
    ∀(r:Fin (Module.finrank ℝ (Model n)+1) → Model n)
      (m:Fin (Module.finrank ℝ (Model n)+1) → ℝ)
      (L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    Tendsto (fun k=>(J.first k).pj₀) atTop (𝓝 r) →
    Tendsto (fun k=>(J.first k).w₀) atTop (𝓝 m) →
    Tendsto (fun k=>(J.first k).L) atTop (𝓝 L) →
    ∀CH CL:ℝ,0 ≤ CH → 0 ≤ CL →
    (∀ᶠ k in atTop,∀d,-CH*‖d‖^2 ≤ (J.first k).H d d) →
    (∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ CL*‖d‖^2) →
    ∀i,(show TangentSpace 𝓘(ℝ,Model n) a from r i)∈minimizingVectors a →
    0 < m i → ∀(e:TangentSpace 𝓘(ℝ,Model n) a) (t lo κo:ℝ),
    ‖e‖=1 → 0 < t → (show TangentSpace 𝓘(ℝ,Model n) a from r i)= (show TangentSpace 𝓘(ℝ,Model n) a from q)+t • e →
    0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e →
    deriv (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=lo →
    iteratedDeriv 2 (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=κo →
    1 < lo → κo<0 →
    ∃rc:Model n,(show TangentSpace 𝓘(ℝ,Model n) c from rc)∈minimizingVectors c ∧
      reverseRay (⟨c,l • rc⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ ∧
    ∃V W:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0 < V d d) ∧
      (∀d e,W d e=W e d) ∧ (∀d,d≠0 → 0 < W d d) ∧
      0 < expJacobian c rc ∧
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ≤expJacobian c rc*(bilinearOperator V).det ∧
      expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
        (lo⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*(bilinearOperator W).det ≤
        (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*lo^n*K*
          (expJacobian (n:=n) a (r i))^2 ∧
      (-κo/lo^2)*(m i)^(n-1)*(bilinearOperator V).det≤(-κc/l^2)*(bilinearOperator W).det := by
  classical
  let : NeZero n:=⟨Nat.ne_of_gt hn⟩
  obtain ⟨δ,hδ,U,hU,h1,HC⟩:=exists_maximum_true_center (n:=n) (M:=M)
  obtain ⟨K,hK,HO⟩:=hmtw.exists_maximum_true_outer hlam hcap
  refine ⟨δ,hδ,K,hK,U,hU,h1,?_⟩
  intro x0 uv huv Lv hv hd α D bminus bplus A₀ B₀ Bc Bo ho hBc hBo hmono hmonoO
    hrange hslope Klip hLip F a c χ N r₀ hχ hr₀ hgood J q β l κc hq he hQ hβ hdC hddC
    hlu hl hl1 hκc r m L hr hm hL CH CL hCH hCL hH hCLbd i hri hmi e t lo κo he1 ht hriq
    hqe hdO hddO hlo hκo
  let ε:=fun k:ℕ=>1/((k:ℝ)+1)
  have hε:Tendsto ε atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨S⟩:=J.exists_outer_diagonal (show ∀k,0 < ε k by intro k; dsimp [ε] <;> positivity)
  have hreg:=J.center_regular uv.1.continuous hv hd hBc hmono Klip hLip hq he hQ hβ hdC hl hl1
  obtain ⟨g,H,σ,hσ,hg,hHs⟩:=S.center_phase_compact hε hreg he hQ hCH hCL hH hCLbd
  let σt:=hσ.tendsto_atTop
  let J':=J.comp σ σt
  let S':=S.comp σ σt
  obtain ⟨rc,hrc,hrev,V,hVs,hVp,hgain,hσc,hdetC⟩:=HC uv.1 uv.2 uv.1.continuous Lv hv hd
    α D bminus bplus A₀ B₀ Bc Bo ho hBc hmono hrange hslope Klip hLip hmtw
    (F.comp σ σt) a c χ N r₀ hχ hr₀ hgood J' (ε ∘ σ) _ S' (hε.comp σt)
    q β l hq he (hQ.comp σt) (hβ.comp σt) hdC hlu hl hl1 g H L hg hHs (hL.comp σt)
  obtain ⟨_,hp,_,_⟩:=F.limit_coordinates hQ
  obtain ⟨hLp,hLs,hker⟩:=J.pole_limit_properties hL hp hr
  have hke:∀d:Model n,L (show Model n from e) d=0:=by
    intro d
    have hh:=hker i d
    have hriq' : r i = q+t • (show Model n from e) := hriq
    have heq:r i-q=t • (show Model n from e):=by
      rw [hriq',add_sub_cancel_left]
    rw [heq,map_smul,smul_apply,smul_eq_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_left ht.ne'
  let f:=frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q
  let gO:=frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) (r i)
  have hf:0 < f (show Model n from e):=by
    calc
      0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e := hqe
      _ = f (show Model n from e) := (frameMetric_center a q (show Model n from e)).symm
  have hfg:f (show Model n from e)≤gO (show Model n from e):=by
    calc
      f (show Model n from e) = inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e :=
        frameMetric_center a q (show Model n from e)
      _ ≤ inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from r i) e := by
        rw [hriq,inner_add_left,inner_smul_left,real_inner_self_eq_norm_sq,he1]
        simp only [one_pow,mul_one,starRingEnd_apply,star_trivial]
        linarith only [ht]
      _ = gO (show Model n from e) := (frameMetric_center a (r i) (show Model n from e)).symm
  have hVL:∀d:Model n,V d d≤L d d+(-κc/l^2)*(f d)^2:=by
    intro d
    have HH:=hgain d
    rw [hddC] at HH
    have hpG:0 ≤ δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d:=by
      rw [frameMetric_center,real_inner_self_eq_norm_sq]
      positivity
    dsimp only [f]
    simp only [neg_div, neg_mul]
    linarith only [HH,hpG]
  have hbc:0 <  -κc/l^2:=div_pos (neg_pos.mpr hκc) (sq_pos_of_pos hl)
  have hbo:0 <  -κo/lo^2:=div_pos (neg_pos.mpr hκo) (sq_pos_of_pos (zero_lt_one.trans hlo))
  have hbase:=functional_rank_one_positive hLs hLp hVp hVL hke hf.ne'
    (hf.trans_le hfg).ne' hmi hbo
  obtain ⟨W,hWs,hWp,hW,hdetO⟩:=HO x0 uv huv α D bminus bplus Bc Bo ho hBo hmonoO
    (F.comp σ σt) a c N J' (ε ∘ σ) S' (hε.comp σt) q β he (hQ.comp σt) (hβ.comp σt)
    r m L (hr.comp σt) (hm.comp σt) (hL.comp σt) i hri hmi lo κo hdO hddO hlo hκo (by
      intro d hd
      have HH:=hbase d hd
      dsimp only [gO] at HH
      simpa only [neg_div, neg_mul, sub_eq_add_neg] using HH)
  have hdet:=bilinear_determinant_gain hLs hVs hWs hke hf hfg hmi hbc hbo hVp hVL (by
    intro d
    have HH:=hW d
    dsimp only [gO]
    simpa only [neg_div, neg_mul, sub_eq_add_neg] using HH)
  refine ⟨rc,hrc,hrev,V,W,hVs,hVp,hWs,hWp,hσc,hdetC,hdetO,?_⟩
  simpa only [Model,finrank_euclideanSpace,Fintype.card_fin] using hdet
end MaximumSimultaneous
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.exists_maximum_simultaneous_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.exists_maximum_simultaneous_oai.{u_1}
