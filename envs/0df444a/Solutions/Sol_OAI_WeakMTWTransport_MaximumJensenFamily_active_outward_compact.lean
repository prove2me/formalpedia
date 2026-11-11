-- Prove2me | solution 1 for OAI.WeakMTWTransport.MaximumJensenFamily.active_outward_compact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:42:21.502136+00:00
-- url     : https://prove2.me/submissions/a8ff696c-bdfb-49bc-9002-2021e48c2f26

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_MinimizingChartParameters
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

variable [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

section
variable [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma isCompact_minimizingChartParameters {a : M} {K : Set M}
    (hK : IsCompact K) (hKs : K⊆(extChartAt 𝓘(ℝ,Model n) a).source) :
    IsCompact (minimizingChartParameters (n := n) a K) := by
  have hc : IsCompact {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈minimizingVectors z.1 ∧ z.1∈K} :=
    (isCompact_total_minimizingVectors (n := n) (M := M)).inter_right
      (hK.isClosed.preimage (FiberBundle.continuous_proj _ _))
  exact hc.image_of_continuousOn ((continuousOn_extChartAt _).mono (fun z hz =>
    (tangent_chart_source_iff _ z).mpr (hKs hz.2)))

end

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartActiveLimit
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

omit [Nonempty M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma compact_in_chart_tail {x : ℕ → M} {a y : M} (hx : Tendsto x atTop (𝓝 y))
    (hy : y∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    ∃ K : Set M,IsCompact K ∧ K⊆(extChartAt 𝓘(ℝ,Model n) a).source ∧
      ∃ N : ℕ,∀ k,x (k+N)∈K := by
  obtain ⟨r,hr,hs⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_source (I := 𝓘(ℝ,Model n)) a) y hy
  have hhalf : 0 < r/2 := half_pos hr
  have he := hx.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hhalf))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  exact ⟨Metric.closedBall y (r/2),isCompact_closedBall y (r/2),
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hs,N,
    fun k=>Metric.ball_subset_closedBall (hN (k+N) (Nat.le_add_left N k))⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActiveGraphLimit
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

lemma chartFiberInverse_at_center (a : M) (p : Model n) :
    chartFiberInverse a ((extChartAt 𝓘(ℝ,Model n) a) a) p=p := by
  dsimp only [chartFiberInverse]
  rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)]
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) a)]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source a)
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_MinimizingCoordinateLimit
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
lemma inverse_mem_minimizingChartParameters {a : M} {K : Set M} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hK : (extChartAt 𝓘(ℝ,Model n) a).symm b∈K)
    (hp : chartFiberInverse a b p∈minimizingVectors ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    (b,p)∈minimizingChartParameters (n := n) a K := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  refine ⟨χ.symm (b,p),?_,χ.right_inv ((tangent_chart_target_iff _ _).mpr hb)⟩
  rw [tangent_chart_symm_trivialization hb]
  exact ⟨hp,hK⟩

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

end WeakMTWTransport

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterRayLimit
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
section CenterRayLimit
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

lemma chartRay_at_center (c:M) (r:Model n) :
    chartRay c (extChartAt 𝓘(ℝ,Model n) c c) r=⟨c,r⟩ := by
  simp only [chartRay,chartFiberInverse_at_center]
  exact congrArg (fun y:M=>(⟨y,r⟩:TangentBundle 𝓘(ℝ,Model n) M))
    ((extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c))

lemma chartRay_tendsto {c:M} {b r:ℕ → Model n} {r0:Model n}
    (hb:Tendsto b atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hr:Tendsto r atTop (𝓝 r0)) :
    Tendsto (fun k=>chartRay c (b k) (r k)) atTop
      (𝓝 (⟨c,r0⟩:TangentBundle 𝓘(ℝ,Model n) M)) := by
  let χ:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨c,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hc:extChartAt 𝓘(ℝ,Model n) c c∈(extChartAt 𝓘(ℝ,Model n) c).target:=
    (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have ht:(extChartAt 𝓘(ℝ,Model n) c c,r0)∈χ.target:=
    (tangent_chart_target_iff _ _).mpr hc
  have H: Tendsto (fun k=>χ.symm (b k,r k)) atTop
      (𝓝 (χ.symm (extChartAt 𝓘(ℝ,Model n) c c,r0))):=
    (continuousAt_extChartAt_symm'' ht).tendsto.comp (hb.prodMk_nhds hr)
  rw [tangent_chart_symm_trivialization hc] at H
  change Tendsto _ _ (𝓝 (chartRay c (extChartAt 𝓘(ℝ,Model n) c c) r0)) at H
  rw [chartRay_at_center] at H
  apply H.congr'
  filter_upwards [hb.eventually ((isOpen_extChartAt_target _).mem_nhds hc)] with k hk
  exact tangent_chart_symm_trivialization hk

end CenterRayLimit
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ParametricActive
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
section ParametricActive
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma activeLogs_iff_minimum {v:M → ℝ} (hv:Continuous v) {x:M}
    {p:TangentSpace 𝓘(ℝ,Model n) x} : p∈activeLogs v x ↔
    p∈minimizingVectors x ∧ ∀ y:M,v (riemannianExp x p)+cost x (riemannianExp x p) ≤ v y+cost x y := by
  constructor
  · rintro ⟨hm,hcontact⟩
    refine ⟨hm,fun y=>?_⟩
    have H:=cTransform_gap_nonneg hv x y
    dsimp only [contactGap] at *
    linarith only [H,hcontact]
  · rintro ⟨hm,hmin⟩
    refine ⟨hm,?_⟩
    obtain ⟨y,hy⟩:=cTransform_gap_zero hv x
    have H:=cTransform_gap_nonneg hv x (riemannianExp x p)
    have HH:=hmin y
    dsimp only [contactGap] at *
    linarith only [H,HH,hy]

omit [CompactSpace M] [Nonempty M] in
lemma continuous_joint_modifiedDatum {v:M → ℝ} (hv:Continuous v)
    (α D:ℝ) {B:ℝ → ℝ} (hB:Continuous B) :
    Continuous (fun q:ℝ×M=>modifiedDatum v α D q.1 B q.2) := by
  exact (hv.comp continuous_snd).add
    (continuous_fst.mul (hB.comp (((hv.comp continuous_snd).sub continuous_const).div_const D)))

lemma modified_active_bundle_limit {v:M → ℝ} (hv:Continuous v)
    {α D:ℝ} {B:ℝ → ℝ} (hB:Continuous B)
    {bk:ℕ → ℝ} {β:ℝ} (hb:Tendsto bk atTop (𝓝 β))
    {Qk:ℕ → TangentBundle 𝓘(ℝ,Model n) M} {Q:TangentBundle 𝓘(ℝ,Model n) M}
    (hQ:Tendsto Qk atTop (𝓝 Q))
    (ha:∀ᶠ k in atTop,(Qk k).2∈activeLogs (modifiedDatum v α D (bk k) B) (Qk k).1) :
    Q.2∈activeLogs (modifiedDatum v α D β B) Q.1 := by
  let : T2Space (TangentBundle 𝓘(ℝ,Model n) M) := bundle_totalSpace_t2
  have hx: Tendsto (fun k=>(Qk k).1) atTop (𝓝 Q.1) :=
    (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).tendsto Q |>.comp hQ
  have hy:=contMDiff_riemannianExp.continuous.tendsto Q |>.comp hQ
  have hm:Q.2∈minimizingVectors Q.1 :=
    (isCompact_total_minimizingVectors (n := n) (M := M)).isClosed.mem_of_tendsto hQ (ha.mono (fun _ h=>h.1))
  apply (activeLogs_iff_minimum (continuous_modifiedDatum hv α D β hB)).mpr
  refine ⟨hm,fun y=>?_⟩
  have hφ:=continuous_joint_modifiedDatum hv α D hB
  have hleft:= (hφ.tendsto (β,riemannianExp Q.1 Q.2) |>.comp (hb.prodMk_nhds hy)).add
    ((hx.dist hy).pow 2 |>.div_const 2)
  have hright:= (hφ.tendsto (β,y) |>.comp (hb.prodMk_nhds tendsto_const_nhds)).add
    ((hx.dist (show Tendsto (fun _:ℕ=>y) atTop (𝓝 y) from tendsto_const_nhds)).pow 2 |>.div_const 2)
  exact le_of_tendsto_of_tendsto hleft hright (ha.mono (fun k hk=>
    ((activeLogs_iff_minimum (continuous_modifiedDatum hv α D (bk k) hB)).mp hk).2 y))

lemma modified_active_coordinates_limit {v:M → ℝ} (hv:Continuous v)
    {α D:ℝ} {B:ℝ → ℝ} (hB:Continuous B)
    {bk:ℕ → ℝ} {β:ℝ} (hb:Tendsto bk atTop (𝓝 β))
    {a:M} {xk pk:ℕ → Model n} {p:Model n}
    (hx:Tendsto xk atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hp:Tendsto pk atTop (𝓝 p))
    (hxt:∀ᶠ k in atTop,xk k∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (ha:∀ᶠ k in atTop,chartFiberInverse a (xk k) (pk k)∈
      activeLogs (modifiedDatum v α D (bk k) B) ((extChartAt 𝓘(ℝ,Model n) a).symm (xk k))) :
    (show TangentSpace 𝓘(ℝ,Model n) a from p)∈activeLogs (modifiedDatum v α D β B) a := by
  let χ:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have ht:(extChartAt 𝓘(ℝ,Model n) a a,p)∈χ.target :=
    (tangent_chart_target_iff _ _).mpr (mem_extChartAt_target a)
  have H:= (continuousAt_extChartAt_symm'' ht).tendsto.comp (hx.prodMk_nhds hp)
  have hcenter:χ.symm (extChartAt 𝓘(ℝ,Model n) a a,p)=
      (⟨a,p⟩:TangentBundle 𝓘(ℝ,Model n) M) := by
    rw [tangent_chart_symm_trivialization (mem_extChartAt_target a),chartFiberInverse_at_center]
    congr 1
    exact (extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)
  rw [hcenter] at H
  apply modified_active_bundle_limit hv hB hb H
  filter_upwards [hxt,ha] with k hk hka
  simp only [Function.comp_apply]
  rwa [tangent_chart_symm_trivialization hk]

end ParametricActive
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ConfigurationCompact
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
section ConfigurationCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma active_configuration_subseq {ι : Type*} [Fintype ι] [Nonempty ι]
    [TopologicalSpace ι] [DiscreteTopology ι]
    {a:M} {v:M → ℝ} (hv:Continuous v) {α D:ℝ} {B:ℝ → ℝ} (hB:Continuous B)
    {β:ℕ → ℝ} {β₀:ℝ} (hβ:Tendsto β atTop (𝓝 β₀))
    {bj p:ℕ → Model n} {p₀:Model n}
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hp:Tendsto p atTop (𝓝 p₀))
    (hbt:∀k,bj k∈(extChartAt 𝓘(ℝ,Model n) a).target)
    {pj:ℕ → ι → Model n} {w:ℕ → ι → ℝ} (i:ℕ → ι)
    (ha:∀k j,chartFiberInverse a (bj k) (pj k j)∈
      activeLogs (modifiedDatum v α D (β k) B) ((extChartAt 𝓘(ℝ,Model n) a).symm (bj k)))
    (hw:∀k j,0 ≤ w k j) (hs:∀k,∑j,w k j=1)
    (hbar:∀k,∑j,w k j • pj k j=p k) :
    ∃σ:ℕ → ℕ,StrictMono σ ∧ ∃r:ι → Model n,∃m:ι → ℝ,∃i₀:ι,
      Tendsto (pj ∘ σ) atTop (𝓝 r) ∧ Tendsto (w ∘ σ) atTop (𝓝 m) ∧
      (∀ᶠ k in atTop,i (σ k)=i₀) ∧
      (∀j,(show TangentSpace 𝓘(ℝ,Model n) a from r j)∈activeLogs (modifiedDatum v α D β₀ B) a) ∧
      (∀j,0 ≤ m j) ∧ ∑j,m j=1 ∧ ∑j,m j • r j=p₀ := by
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  have hat:χ a∈χ.target := mem_extChartAt_target a
  have hy:Tendsto (fun k=>χ.symm (bj k)) atTop (𝓝 a) := by
    have H:=(continuousAt_extChartAt_symm'' hat).tendsto.comp hb
    rwa [χ.left_inv (mem_extChartAt_source a)] at H
  obtain ⟨K,hK,hKs,N,hN⟩:=compact_in_chart_tail (n := n) (a := a) hy (mem_extChartAt_source a)
  let shift:=fun k:ℕ=>k+N
  have hshift:Tendsto shift atTop atTop := tendsto_add_atTop_nat N
  let C:=minimizingChartParameters (n := n) a K
  have hC:IsCompact C := isCompact_minimizingChartParameters hK hKs
  let S:= {q:EnvelopeData (Model n) ι | (∀j,(q.1.1,q.1.2 j)∈C) ∧
    (∀j,0 ≤ q.2.1 j) ∧ ∑j,q.2.1 j=1 ∧ q.2.2∈Icc 0 0}
  have hc:IsCompact (S×ˢ(univ:Set ι)) := (compact_common_base_configurations hC 0).prod isCompact_univ
  let f:ℕ → EnvelopeData (Model n) ι × ι := fun k=>(((bj (shift k),pj (shift k)),(w (shift k),0)),i (shift k))
  have hf:∀k,f k∈S×ˢ(univ:Set ι) := by
    intro k
    refine ⟨⟨?_,hw _,hs _,le_rfl,le_rfl⟩,mem_univ _⟩
    intro j
    exact inverse_mem_minimizingChartParameters (hbt _) (hN k) (ha _ j).1
  obtain ⟨q,hq,τ,hτ,hlim⟩:=hc.isSeqCompact hf
  let σ:=shift ∘ τ
  have hσ:StrictMono σ := fun k l h=>Nat.add_lt_add_right (hτ h) N
  have hr:Tendsto (pj ∘ σ) atTop (𝓝 q.1.1.2) := hlim.fst_nhds.fst_nhds.snd_nhds
  have hm:Tendsto (w ∘ σ) atTop (𝓝 q.1.2.1) := hlim.fst_nhds.snd_nhds.fst_nhds
  have hi:∀ᶠ k in atTop,i (σ k)=q.2 := by
    exact hlim.snd_nhds.eventually ((isOpen_discrete {q.2}).mem_nhds rfl)
  refine ⟨σ,hσ,q.1.1.2,q.1.2.1,q.2,hr,hm,hi,?_,hq.1.2.1,hq.1.2.2.1,?_⟩
  · intro j
    apply modified_active_coordinates_limit hv hB (hβ.comp hσ.tendsto_atTop)
      (hb.comp hσ.tendsto_atTop) ((tendsto_pi_nhds.mp hr) j)
      (Eventually.of_forall (fun k=>hbt (σ k)))
      (Eventually.of_forall (fun k=>ha (σ k) j))
  · have H:Tendsto (fun k=>∑j,w (σ k) j • pj (σ k) j) atTop
        (𝓝 (∑j,q.1.2.1 j • q.1.1.2 j)) := by
      apply tendsto_finsetSum
      intro j _
      exact ((tendsto_pi_nhds.mp hm) j).smul ((tendsto_pi_nhds.mp hr) j)
    simp only [hbar] at H
    exact tendsto_nhds_unique H (hp.comp hσ.tendsto_atTop)
end ConfigurationCompact
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OutwardClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
section OutwardClosed
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma outward_closed_conditions {p r e:E} {d w a D ν:ℝ}
    (he:‖e‖=1) (hp:0 < inner ℝ p e) (hd:0 < d) (hr:r=p+d • e)
    (ha:0 < a) (hD:0 < D) (hq:a*D ≤ (inner ℝ p e)^2)
    (hm:ν*D/(inner ℝ p e) ≤ w*d) (hdb:d ≤ 3*D/(2*(inner ℝ p e))) :
    ν*D ≤ w*inner ℝ p (r-p) ∧
    a*D*‖r-p‖^2 ≤ (inner ℝ p (r-p))^2 ∧
    inner ℝ p (r-p) ≤ 3*D/2 ∧
    ‖r-p‖^2 ≤ (9/(4*a))*D := by
  have hrp:r-p=d • e:=by rw [hr]; abel
  have hi:inner ℝ p (r-p)=d*inner ℝ p e:=by rw [hrp,real_inner_smul_right]
  have hn:‖r-p‖=d:=by rw [hrp,norm_smul,Real.norm_eq_abs,abs_of_pos hd,he,mul_one]
  have Hm:ν*D ≤ w*d*(inner ℝ p e):=(div_le_iff₀ hp).mp hm
  have Hdb:d*(2*inner ℝ p e) ≤ 3*D:=(le_div_iff₀ (mul_pos (by norm_num) hp)).mp hdb
  have Hsq:(d*inner ℝ p e)^2 ≤ (3*D/2)^2:=by
    apply (sq_le_sq₀ (mul_nonneg hd.le hp.le) (by positivity)).mpr
    linarith only [Hdb]
  have Hq:=mul_le_mul_of_nonneg_right hq (sq_nonneg d)
  have Hlast:d^2 ≤ (9/(4*a))*D:=by
    apply (mul_le_mul_iff_right₀ (mul_pos ha hD)).mp
    have hh:(a*D)*((9/(4*a))*D)=(3*D/2)^2:=by field_simp <;> ring
    rw [hh]
    calc a*D*d^2 ≤ (inner ℝ p e)^2*d^2:=Hq
         _ = (d*inner ℝ p e)^2:=by ring
         _ ≤ _:=Hsq
  refine ⟨?_,?_,?_,?_⟩
  · rw [hi]; nlinarith only [Hm]
  · rw [hn,hi]; nlinarith only [Hq]
  · rw [hi]; linarith only [Hdb]
  · rwa [hn]

lemma outward_direction_of_closed_conditions {p r:E} {w a D ν:ℝ}
    (hw:0 < w) (_:0 < a) (hD:0 < D) (hν:0 < ν)
    (hm:ν*D ≤ w*inner ℝ p (r-p))
    (hq:a*D*‖r-p‖^2 ≤ (inner ℝ p (r-p))^2)
    (hi:inner ℝ p (r-p) ≤ 3*D/2)
    (hn:‖r-p‖^2 ≤ (9/(4*a))*D) :
    ∃e:E,∃d:ℝ,‖e‖=1 ∧ 0 < d ∧ r=p+d • e ∧
      0 < inner ℝ p e ∧ a*D ≤ (inner ℝ p e)^2 ∧
      ν*D/(inner ℝ p e) ≤ w*d ∧
      d ≤ 3*D/(2*(inner ℝ p e)) ∧
      ‖r‖^2-‖p‖^2 ≤ (3+9/(4*a))*D := by
  have hp:0 < inner ℝ p (r-p):=by
    have H:0 < w*inner ℝ p (r-p):=(mul_pos hν hD).trans_le hm
    exact (mul_pos_iff_of_pos_left hw).mp H
  have hv:r-p≠0:=by intro H; rw [H,inner_zero_right] at hp; exact lt_irrefl _ hp
  have hd:0 < ‖r-p‖:=norm_pos_iff.mpr hv
  let e:E:=‖r-p‖⁻¹ • (r-p)
  have he:‖e‖=1:=by simp only [e,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hd,inv_mul_cancel₀ hd.ne']
  have hr:r=p+‖r-p‖ • e:=by
    simp only [e,smul_smul,mul_inv_cancel₀ hd.ne',one_smul]
    abel
  have hpe:inner ℝ p e=inner ℝ p (r-p)/‖r-p‖:=by
    simp only [e,real_inner_smul_right,div_eq_mul_inv,mul_comm]
  have hpep:0 < inner ℝ p e:=by rw [hpe]; exact div_pos hp hd
  refine ⟨e,‖r-p‖,he,hd,hr,hpep,?_,?_,?_,?_⟩
  · rw [hpe,div_pow]
    exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr hq
  · apply (div_le_iff₀ hpep).mpr
    rw [hpe]
    have HH:w*‖r-p‖*(inner ℝ p (r-p)/‖r-p‖)=w*inner ℝ p (r-p):=by
      field_simp
    rwa [HH]
  · apply (le_div_iff₀ (mul_pos (by norm_num) hpep)).mpr
    rw [hpe]
    have H:‖r-p‖*(2*(inner ℝ p (r-p)/‖r-p‖))=2*inner ℝ p (r-p):=by field_simp
    rw [H]
    linarith only [hi]
  · have H:‖r‖^2=‖p‖^2+2*inner ℝ p (r-p)+‖r-p‖^2:=by
      conv_lhs => rw [show r=p+(r-p) by abel]
      exact norm_add_sq_real _ _
    nlinarith only [H,hi,hn]

end OutwardClosed
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FrameOutwardLimit
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
section FrameOutwardLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma moving_frame_outward_limit {a:M} {b p r:ℕ → Model n} {q s:Model n}
    {w:ℕ → ℝ} {m μ κ D ν:ℝ}
    (hb:Tendsto b atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hp:Tendsto p atTop (𝓝 q)) (hr:Tendsto r atTop (𝓝 s))
    (hw:Tendsto w atTop (𝓝 m)) (hμ:0 < μ) (hκ:0 < κ) (hD:0 < D) (hν:0 < ν)
    (hsel:∀ᶠ k in atTop,
      let A:=chartFiberInverse a (b k)
      ∃e:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm (b k)),∃d:ℝ,
        ‖e‖=1 ∧ 0 < inner ℝ (A (p k)) e ∧ κ*D ≤ (inner ℝ (A (p k)) e)^2 ∧
        0 < d ∧ A (r k)=A (p k)+d • e ∧ μ ≤ w k ∧
        ν*D/(inner ℝ (A (p k)) e) ≤ w k*d ∧
        d ≤ 3*D/(2*(inner ℝ (A (p k)) e))) :
    μ ≤ m ∧ ∃e:TangentSpace 𝓘(ℝ,Model n) a,∃d:ℝ,‖e‖=1 ∧ 0 < d ∧
      (show TangentSpace 𝓘(ℝ,Model n) a from s)=(show TangentSpace 𝓘(ℝ,Model n) a from q)+d • e ∧
      0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e ∧
      κ*D ≤ (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)^2 ∧
      ν*D/(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e) ≤ m*d ∧
      d ≤ 3*D/(2*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)) ∧
      ‖show TangentSpace 𝓘(ℝ,Model n) a from s‖^2-
        ‖show TangentSpace 𝓘(ℝ,Model n) a from q‖^2 ≤ (3+9/(4*κ))*D := by
  have hbase:(extChartAt 𝓘(ℝ,Model n) a a)∈(extChartAt 𝓘(ℝ,Model n) a).target:=mem_extChartAt_target a
  have hbt:∀ᶠ k in atTop,b k∈(extChartAt 𝓘(ℝ,Model n) a).target:=
    hb.eventually ((isOpen_extChartAt_target a).mem_nhds hbase)
  have hG:=(frameMetric_continuousAt hbase).tendsto.comp hb
  have hdiff:=hr.sub hp
  have hI:=tendsto_clm_apply (tendsto_clm_apply hG hp) hdiff
  have hN:=tendsto_clm_apply (tendsto_clm_apply hG hdiff) hdiff
  simp only [frameMetric_center] at hI hN
  have H:∀ᶠ k in atTop,μ ≤ w k ∧
      ν*D ≤ w k*frameMetric a (b k) (p k) (r k-p k) ∧
      κ*D*frameMetric a (b k) (r k-p k) (r k-p k) ≤
        (frameMetric a (b k) (p k) (r k-p k))^2 ∧
      frameMetric a (b k) (p k) (r k-p k) ≤ 3*D/2 ∧
      frameMetric a (b k) (r k-p k) (r k-p k) ≤ (9/(4*κ))*D:=by
    filter_upwards [hsel,hbt] with k hk hbk
    dsimp only at hk
    obtain ⟨e,d,he,hep,hq,hd,hrd,hm,hmom,hdb⟩:=hk
    have HH:=outward_closed_conditions he hep hd hrd hκ hD hq hmom hdb
    simp only [frameMetric_apply hbk]
    simp only [map_sub,real_inner_self_eq_norm_sq]
    exact ⟨hm,HH⟩
  have Hm:μ ≤ m:=ge_of_tendsto hw (H.mono (fun k hk=>hk.1))
  refine ⟨Hm,?_⟩
  apply outward_direction_of_closed_conditions (hμ.trans_le Hm) hκ hD hν
  · exact ge_of_tendsto (hw.mul hI) (H.mono (fun k hk=>hk.2.1))
  · have HH:=le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hN) (hI.pow 2)
      (H.mono (fun k hk=>hk.2.2.1))
    rw [show inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from s-q) (s-q)=
      ‖show TangentSpace 𝓘(ℝ,Model n) a from s-q‖^2 from
        @real_inner_self_eq_norm_sq (TangentSpace 𝓘(ℝ,Model n) a) _ _ (s-q)] at HH
    exact HH
  · exact le_of_tendsto hI (H.mono (fun k hk=>hk.2.2.2.1))
  · have HH:=le_of_tendsto hN (H.mono (fun k hk=>hk.2.2.2.2))
    rw [show inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from s-q) (s-q)=
      ‖show TangentSpace 𝓘(ℝ,Model n) a from s-q‖^2 from
        @real_inner_self_eq_norm_sq (TangentSpace 𝓘(ℝ,Model n) a) _ _ (s-q)] at HH
    exact HH

end FrameOutwardLimit
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumActiveCompact
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
section MaximumActiveCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumJensenFamily.active_subseq
    {hmtw:WeakMTW (n:=n) (M:=M)} {v:M → ℝ} {hv:Continuous v}
    {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    {q:Model n} {β:ℝ} (hb:Tendsto F.b atTop (𝓝 β))
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    (i:ℕ → Fin (Module.finrank ℝ (Model n)+1)) :
    ∃σ:ℕ → ℕ,StrictMono σ ∧
      ∃r:Fin (Module.finrank ℝ (Model n)+1) → Model n,
      ∃m:Fin (Module.finrank ℝ (Model n)+1) → ℝ,
      ∃i₀:Fin (Module.finrank ℝ (Model n)+1),
        Tendsto (fun k=>(J.first (σ k)).pj₀) atTop (𝓝 r) ∧
        Tendsto (fun k=>(J.first (σ k)).w₀) atTop (𝓝 m) ∧
        (∀ᶠ k in atTop,i (σ k)=i₀) ∧
        (∀j,(show TangentSpace 𝓘(ℝ,Model n) a from r j)∈
          activeLogs (modifiedDatum v α D β Bo) a) ∧
        (∀j,0 ≤ m j) ∧ ∑j,m j=1 ∧ ∑j,m j • r j=q := by
  obtain ⟨hbase,hvel,_,_⟩:=F.limit_coordinates hQ
  exact active_configuration_subseq hv ho hb hbase hvel
    (fun k=>(extChartAt 𝓘(ℝ,Model n) a).map_source (J.poleSource k)) i
    (fun k j=>(J.first k).activeLimit j) (fun k j=>(J.first k).nonnegLimit j)
    (fun k=>(J.first k).totalLimit) (fun k=>(J.first k).baryLimit)

end MaximumActiveCompact
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumOutwardCompact
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
section MaximumOutwardCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumJensenFamily.active_outward_compact_oai
    {hmtw:WeakMTW (n:=n) (M:=M)} {v:M → ℝ} {hv:Continuous v}
    {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    {q:Model n} {β μ ν κ eta U:ℝ} (hb:Tendsto F.b atTop (𝓝 β))
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    (hμ:0 < μ) (hν:0 < ν) (hκ:0 < κ) (hD:0 < D)
    (hsel:∀ᶠ k in atTop,
      let b:=graphBaseCoordinate a (F.row k).q.1
      let A:=chartFiberInverse a b
      let P:=A (graphVelocityCoordinate a (F.row k).q.1)
      let si:=fun i=>(v (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b)
        (A ((J.first k).pj₀ i)))-α)/D
      ∃i:Fin (Module.finrank ℝ (Model n)+1),
      ∃e:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b),∃d:ℝ,
        ‖e‖=1 ∧ 0 < inner ℝ P e ∧ κ*D ≤ (inner ℝ P e)^2 ∧ 0 < d ∧
        A ((J.first k).pj₀ i)=P+d • e ∧ μ ≤ (J.first k).w₀ i ∧
        ν*D/(inner ℝ P e) ≤ (J.first k).w₀ i*d ∧
        d ≤ 3*D/(2*(inner ℝ P e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧ Bo (si i) ≤ U) :
    ∃σ:ℕ → ℕ,StrictMono σ ∧
      ∃r:Fin (Module.finrank ℝ (Model n)+1) → Model n,
      ∃m:Fin (Module.finrank ℝ (Model n)+1) → ℝ,
      ∃i₀:Fin (Module.finrank ℝ (Model n)+1),
        Tendsto (fun k=>(J.first (σ k)).pj₀) atTop (𝓝 r) ∧
        Tendsto (fun k=>(J.first (σ k)).w₀) atTop (𝓝 m) ∧
        (∀j,(show TangentSpace 𝓘(ℝ,Model n) a from r j)∈
          activeLogs (modifiedDatum v α D β Bo) a) ∧
        (∀j,0 ≤ m j) ∧ ∑j,m j=1 ∧ ∑j,m j • r j=q ∧ μ ≤ m i₀ ∧
        (∀ᶠ k in atTop,μ ≤ (J.first (σ k)).w₀ i₀) ∧
        -2*eta ≤ (v (riemannianExp a (r i₀))-α)/D ∧
        (v (riemannianExp a (r i₀))-α)/D ≤ 1-eta ∧
        Bo ((v (riemannianExp a (r i₀))-α)/D) ≤ U ∧
        ∃e:TangentSpace 𝓘(ℝ,Model n) a,∃d:ℝ,‖e‖=1 ∧ 0 < d ∧
          (show TangentSpace 𝓘(ℝ,Model n) a from r i₀)=
            (show TangentSpace 𝓘(ℝ,Model n) a from q)+d • e ∧
          0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e ∧
          κ*D ≤ (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)^2 ∧
          ν*D/(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e) ≤ m i₀*d ∧
          d ≤ 3*D/(2*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)) ∧
          ‖show TangentSpace 𝓘(ℝ,Model n) a from r i₀‖^2-
            ‖show TangentSpace 𝓘(ℝ,Model n) a from q‖^2 ≤ (3+9/(4*κ))*D := by
  classical
  let b:=fun k=>graphBaseCoordinate a (F.row k).q.1
  let p:=fun k=>graphVelocityCoordinate a (F.row k).q.1
  let S:=fun k (i:Fin (Module.finrank ℝ (Model n)+1))=>
    ∃e:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm (b k)),∃d:ℝ,
      ‖e‖=1 ∧ 0 < inner ℝ (chartFiberInverse a (b k) (p k)) e ∧
      κ*D ≤ (inner ℝ (chartFiberInverse a (b k) (p k)) e)^2 ∧ 0 < d ∧
      chartFiberInverse a (b k) ((J.first k).pj₀ i)=
        chartFiberInverse a (b k) (p k)+d • e ∧ μ ≤ (J.first k).w₀ i ∧
      ν*D/(inner ℝ (chartFiberInverse a (b k) (p k)) e) ≤ (J.first k).w₀ i*d ∧
      d ≤ 3*D/(2*(inner ℝ (chartFiberInverse a (b k) (p k)) e)) ∧
      -2*eta ≤ (v (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm (b k))
        (chartFiberInverse a (b k) ((J.first k).pj₀ i)))-α)/D ∧
      (v (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm (b k))
        (chartFiberInverse a (b k) ((J.first k).pj₀ i)))-α)/D < 1-eta ∧
      Bo ((v (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm (b k))
        (chartFiberInverse a (b k) ((J.first k).pj₀ i)))-α)/D) ≤ U
  let i:=fun k=>if h:∃j,S k j then Classical.choose h else 0
  have Hi:∀ᶠ k in atTop,S k (i k):=by
    filter_upwards [hsel] with k hk
    change ∃j,S k j at hk
    dsimp only [i]
    rw [dite_eq_left hk]
    exact Classical.choose_spec hk
  obtain ⟨σ,hσ,r,m,i₀,hr,hm,hfix,hact,hmn,hmt,hbar⟩:=J.active_subseq hb hQ i
  have Hs:∀ᶠ k in atTop,S (σ k) i₀:=by
    filter_upwards [hσ.tendsto_atTop.eventually Hi,hfix] with k hk hki
    rwa [hki] at hk
  obtain ⟨hbase,hvel,_,_⟩:=F.limit_coordinates hQ
  have hbs:=hbase.comp hσ.tendsto_atTop
  have hps:=hvel.comp hσ.tendsto_atTop
  have hrs:=tendsto_pi_nhds.mp hr i₀
  have hms:=tendsto_pi_nhds.mp hm i₀
  have hdir:=moving_frame_outward_limit hbs hps hrs hms hμ hκ hD hν
  have HD:μ ≤ m i₀ ∧ _:=hdir (by
    filter_upwards [Hs] with k hk
    obtain ⟨e,d,he,hep,hq,hd,hrd,hm',hmom,hdb,_,_,_⟩:=hk
    exact ⟨e,d,he,hep,hq,hd,hrd,hm',hmom,hdb⟩)
  have hT: Tendsto (fun k=>(v (riemannianExp
      ((extChartAt 𝓘(ℝ,Model n) a).symm (b (σ k)))
      (chartFiberInverse a (b (σ k)) ((J.first (σ k)).pj₀ i₀)))-α)/D)
      atTop (𝓝 ((v (riemannianExp a (r i₀))-α)/D)):=by
    have he:=contMDiff_riemannianExp.continuous.continuousAt.tendsto.comp (chartRay_tendsto hbs hrs)
    exact ((hv.continuousAt.tendsto.comp he).sub tendsto_const_nhds).div_const D
  refine ⟨σ,hσ,r,m,i₀,hr,hm,hact,hmn,hmt,hbar,HD.1,?_,?_,?_,?_,HD.2⟩
  · exact Hs.mono (fun k hk=>by obtain ⟨e,d,_,_,_,_,_,hh,_⟩:=hk; exact hh)
  · apply ge_of_tendsto hT
    exact Hs.mono (fun k hk=>by obtain ⟨e,d,_,_,_,_,_,_,_,_,hh,_⟩:=hk; exact hh)
  · apply le_of_tendsto hT
    exact Hs.mono (fun k hk=>by obtain ⟨e,d,_,_,_,_,_,_,_,_,_,hh,_⟩:=hk; exact hh.le)
  · apply le_of_tendsto (ho.continuousAt.tendsto.comp hT)
    exact Hs.mono (fun k hk=>by obtain ⟨e,d,_,_,_,_,_,_,_,_,_,_,hh⟩:=hk; exact hh)

end MaximumOutwardCompact
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.MaximumJensenFamily.active_outward_compact_oai.{u_1} := @OAI.WeakMTWTransport.MaximumJensenFamily.active_outward_compact_oai.{u_1}
