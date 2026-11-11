-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_maximum_center_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:42:27.105606+00:00
-- url     : https://prove2.me/submissions/4fbdc862-13e7-4bee-8428-490aafe72576

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
import Theorems.Thm_OAI_WeakMTWTransport_exists_actual_center_sequential_gain

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport

lemma continuous_scalar_family_deriv {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (fun p:ℝ×ℝ=>deriv (fun s=>Φ (p.1,s)) p.2) := by
  have heq (p:ℝ×ℝ) := (scalar_family_hasDeriv hΦ p).deriv
  simp_rw [heq]
  exact (contDiff_infty_iff_fderiv.mp hΦ).2.continuous.clm_apply continuous_const

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

lemma mem_minimizingChartParameters {a : M} {K : Set M}
    (hKs : K⊆(extChartAt 𝓘(ℝ,Model n) a).source) {q : Model n×Model n}
    (hq : q∈minimizingChartParameters (n := n) a K) :
    q.1∈(extChartAt 𝓘(ℝ,Model n) a).target ∧
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1∈K ∧
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm q.1) q.2∈
        minimizingVectors ((extChartAt 𝓘(ℝ,Model n) a).symm q.1)) := by
  obtain ⟨z,hz,rfl⟩ := hq
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  have hzs : z∈χ.source := (tangent_chart_source_iff _ z).mpr (hKs hz.2)
  have hb : (χ z).1∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (tangent_chart_target_iff _ _).mp (χ.map_source hzs)
  refine ⟨hb,?_⟩
  have H : (χ.symm (χ z)).1∈K ∧ (χ.symm (χ z)).2∈minimizingVectors (χ.symm (χ z)).1 := by
    rw [χ.left_inv hzs]
    exact ⟨hz.2,hz.1⟩
  rw [tangent_chart_symm_trivialization hb] at H
  exact H

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

omit [Nonempty M] in
lemma minimizing_coordinates_tail_subseq {a : M} {bj pj : ℕ → Model n}
    (hb : Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hbt : ∀ i,bj i∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hpm : ∀ i,chartFiberInverse a (bj i) (pj i)∈
      minimizingVectors ((extChartAt 𝓘(ℝ,Model n) a).symm (bj i))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ p : Model n,
      (show TangentSpace 𝓘(ℝ,Model n) a from p)∈minimizingVectors a ∧
      Tendsto (pj ∘ σ) atTop (𝓝 p) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  have ha := χ.map_source (mem_extChartAt_source a)
  have hy : Tendsto (fun i=>χ.symm (bj i)) atTop (𝓝 a) := by
    have H := (continuousAt_extChartAt_symm'' ha).tendsto.comp hb
    rwa [χ.left_inv (mem_extChartAt_source a)] at H
  obtain ⟨K,hK,hKs,N,hN⟩ := compact_in_chart_tail (n := n) (a := a) hy (mem_extChartAt_source a)
  have hshift : Tendsto (fun k:ℕ=>k+N) atTop atTop := tendsto_add_atTop_nat N
  have hin (k : ℕ) : (bj (k+N),pj (k+N))∈minimizingChartParameters (n := n) a K :=
    inverse_mem_minimizingChartParameters (hbt _) (hN k) (hpm _)
  obtain ⟨q,hq,σ,hσ,hlim⟩ :=
    (isCompact_minimizingChartParameters hK hKs).isSeqCompact hin
  have hbase : q.1=χ a := tendsto_nhds_unique hlim.fst_nhds ((hb.comp hshift).comp hσ.tendsto_atTop)
  have hmin := (mem_minimizingChartParameters hKs hq).2.2
  change chartFiberInverse a q.1 q.2∈minimizingVectors (χ.symm q.1) at hmin
  rw [hbase,chartFiberInverse_at_center,χ.left_inv (mem_extChartAt_source a)] at hmin
  exact ⟨fun k=>σ k+N,fun i j hij=>Nat.add_lt_add_right (hσ hij) N,q.2,hmin,hlim.snd_nhds⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CenterSupportFamily
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

omit [Nonempty M] in
lemma center_support_family_subseq {c : M} {u v : M → ℝ} {Φ : ℝ×ℝ → ℝ}
    {γj lj τj : ℕ → ℝ} {xj : ℕ → Model n} {zj : ℕ → M}
    (R : ∀ i,TrueCenterRow c u v (fun s=>Φ (γj i,s)) (xj i) (zj i) (τj i) (lj i))
    (hx : Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ r : Model n,
      (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c ∧
      Tendsto (fun i=>(R (σ i)).r) atTop (𝓝 r) :=
  minimizing_coordinates_tail_subseq hx (fun i=>(R i).chart) (fun i=>(R i).minimizing)

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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearClose
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma bilinear_quadratic_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E →L[ℝ] ℝ) (d:E) : |A d d|≤‖A‖*‖d‖^2 := by
  calc
    |A d d| = ‖A d d‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖A d‖*‖d‖ := (A d).le_opNorm d
    _ ≤ (‖A‖*‖d‖)*‖d‖ := mul_le_mul_of_nonneg_right (A.le_opNorm d) (norm_nonneg d)
    _ = ‖A‖*‖d‖^2 := by ring

lemma bilinear_quadratic_close {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E →L[ℝ] E →L[ℝ] ℝ} {ε:ℝ} (h : ‖A-B‖≤ε) (d:E) :
    A d d≤B d d+ε*‖d‖^2 := by
  have H := (le_abs_self ((A-B) d d)).trans (bilinear_quadratic_norm_bound (A-B) d)
  have HH := H.trans (mul_le_mul_of_nonneg_right h (sq_nonneg ‖d‖))
  simpa only [_root_.sub_apply,sub_le_iff_le_add,add_comm] using HH

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterSequenceCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section CenterSequenceCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_actual_center_gain :
    ∃ c0>0,∀ᶠ l : ℝ in 𝓝 1, 0<l → l<1 →
      ∀ (a c : M) (u v : M → ℝ) (Φ : ℝ×ℝ → ℝ) (γ : ℝ),
      Continuous v → ContDiffAt ℝ ∞ Φ (γ,v c) →
      deriv (fun s=>Φ (γ,s)) (v c)=l →
      ∀ (γj lj τj tj : ℕ → ℝ) (xj bj qj : ℕ → Model n) (zj : ℕ → M)
        (F : ℕ → Model n → ℝ),
      CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F →
      ∀ q : Model n,
      (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a →
      riemannianExp a q=c →
      Tendsto γj atTop (𝓝 γ) → Tendsto lj atTop (𝓝 l) →
      Tendsto τj atTop (𝓝 0) → Tendsto tj atTop (𝓝 1) →
      Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) →
      Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) →
      Tendsto qj atTop (𝓝 q) →
      (∀ᶠ i in atTop,0<τj i) → ∀ L : ℝ≥0,
      (∀ᶠ i in atTop,LipschitzWith L (fun y=>Φ (γj i,v y))) →
      ∀ ε : ℝ,0<ε →
      ∀ᶠ i in atTop,∀ d : Model n,
        c0*(1-l)*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
          (iteratedDeriv 2 (fun s=>Φ (γ,s)) (v c)/l^2)*
            (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤
        coordinateCenterMatrix a (tj i) (hopfLax (τj i) (fun y=>Φ (γj i,v y)))
          (bj i) (qj i) d d := by
  obtain ⟨c0,hc0,H⟩ := exists_actual_center_sequential_gain (n := n) (M := M)
  refine ⟨c0,hc0,?_⟩
  filter_upwards [H] with l hgain
  intro hl hl1 a c u v Φ γ hv hΦ hder γj lj τj tj xj bj qj zj F D q hq he
    hγ hlm hτ ht hx hb hqq hτpos L hLip ε hε
  by_contra h
  have hf := not_eventually.mp h
  choose σ hσge hbad using frequently_atTop.mp hf
  have hσ : Tendsto σ atTop atTop := tendsto_atTop_mono hσge tendsto_id
  let D1 := D.comp σ hσ
  obtain ⟨κ,hκ,r,hr,hrr⟩ := center_support_family_subseq D1.row (hx.comp hσ)
  let D2 := D1.comp κ hκ.tendsto_atTop
  have Hlow := hgain hl hl1 a c u v Φ γ hv hΦ hder
    ((γj ∘ σ) ∘ κ) ((lj ∘ σ) ∘ κ) ((τj ∘ σ) ∘ κ) ((tj ∘ σ) ∘ κ)
    ((xj ∘ σ) ∘ κ) ((bj ∘ σ) ∘ κ) ((qj ∘ σ) ∘ κ) ((zj ∘ σ) ∘ κ)
    ((F ∘ σ) ∘ κ) D2 r q hr hq he
    ((hγ.comp hσ).comp hκ.tendsto_atTop) ((hlm.comp hσ).comp hκ.tendsto_atTop)
    ((hτ.comp hσ).comp hκ.tendsto_atTop) ((ht.comp hσ).comp hκ.tendsto_atTop)
    ((hx.comp hσ).comp hκ.tendsto_atTop) ((hb.comp hσ).comp hκ.tendsto_atTop)
    ((hqq.comp hσ).comp hκ.tendsto_atTop) hrr
    (hκ.tendsto_atTop.eventually (hσ.eventually hτpos)) L
    (hκ.tendsto_atTop.eventually (hσ.eventually hLip)) ε hε
  obtain ⟨i,hi⟩ := Hlow.exists
  exact hbad (κ i) hi

end CenterSequenceCompact
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_Diagonal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma diagonal_tendsto_of_close {X : Type*} [PseudoMetricSpace X]
    {f a : ℕ → X} {x : X} {ε : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 x)) (hε : Tendsto ε atTop (𝓝 0))
    (hclose : ∀ᶠ k in atTop,dist (f k) (a k)≤ε k) : Tendsto f atTop (𝓝 x) := by
  apply tendsto_of_tendsto_of_dist ha
  exact squeeze_zero' (Eventually.of_forall (fun _=>dist_nonneg)) (hclose.mono (fun k hk=>by simpa only [dist_comm] using hk)) hε

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

lemma MaximumDiagonal.limits (J : MaximumJensenFamily hmtw hv ho F a c N)
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    (hε : Tendsto ε atTop (𝓝 0)) {q : Model n}
    (hQ : Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M))) (hc : riemannianExp a q=c) :
    Tendsto (fun k=>graphBaseCoordinate a (J.samplePoint k (S.ν k)).1) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) ∧
    Tendsto (fun k=>graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1) atTop (𝓝 q) ∧
    Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) ∧
    Tendsto (fun k=>J.sampleGradient k (S.ν k)) atTop (𝓝 0) := by
  obtain ⟨hb,hp,hz,hy⟩ := F.limit_coordinates hQ
  rw [hc] at hy
  have hY := ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds
    (mem_extChartAt_source (I := 𝓘(ℝ,Model n)) c))).tendsto.comp hy
  refine ⟨diagonal_tendsto_of_close hb hε (Eventually.of_forall (fun k=>(S.baseClose k).le)),
    diagonal_tendsto_of_close hp hε (Eventually.of_forall (fun k=>(S.velocityClose k).le)),
    diagonal_tendsto_of_close hY hε (Eventually.of_forall (fun k=>(S.centerClose k).le)),?_⟩
  apply diagonal_tendsto_of_close tendsto_const_nhds hε
  exact Eventually.of_forall (fun k=>by simpa only [dist_zero_right] using (S.gradientClose k).le)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumCenterSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumCenterSequence
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.center_tendsto {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    (hx : Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c))) :
    Tendsto (fun k=>(J.sample k).Y ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 c) := by
  let χ := extChartAt 𝓘(ℝ,Model n) c
  have H := (continuousAt_extChartAt_symm'' (χ.map_source (mem_extChartAt_source c))).tendsto.comp hx
  rw [χ.left_inv (mem_extChartAt_source c)] at H
  apply H.congr
  intro k
  exact χ.left_inv ((J.sample k).samples (J.sampleIndex k (S.ν k))).1

lemma MaximumDiagonal.slope_tendsto {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    (hBc : ContDiff ℝ ∞ Bc) {β : ℝ} (hβ : Tendsto F.b atTop (𝓝 β))
    (hx : Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c))) :
    Tendsto (fun k=>J.sampleSlope k (S.ν k)) atTop
      (𝓝 (deriv (fun s=>modifiedScalar α D Bc (β,s)) (v c))) := by
  exact ((continuous_scalar_family_deriv (modifiedScalar_contDiff hBc α D)).tendsto (β,v c)).comp
    (hβ.prodMk_nhds ((hv.tendsto c).comp (S.center_tendsto hx)))

end MaximumCenterSequence
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumCenterLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumCenterLower
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_maximum_center_gain_oai :
    ∃ c0>0,∀ᶠ l:ℝ in 𝓝 1,0<l → l<1 →
    ∀ (hmtw : WeakMTW (n := n) (M := M)) (u v : M → ℝ),
    Continuous u → ∀ (Lv : ℝ≥0) (hv : LipschitzWith Lv v),
    IsCostDualPair u v →
    ∀ (α D bminus bplus : ℝ) (Bc Bo : ℝ → ℝ) (ho : Continuous Bo),
    ContDiff ℝ ∞ Bc →
    (∀ b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s))) →
    ∀ L:ℝ≥0,(∀ b∈Icc bminus bplus,LipschitzWith L (modifiedDatum v α D b Bc)) →
    ∀ (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo) (a c:M) (N:Set (Model n)),
    ∀ J : MaximumJensenFamily hmtw hv.continuous ho F a c N,
    ∀ (q:Model n) (β:ℝ),
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a →
    riemannianExp a q=c →
    Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto F.b atTop (𝓝 β) →
    deriv (fun s=>modifiedScalar α D Bc (β,s)) (v c)=l →
    ∀ ε:ℝ,0<ε → ∀ᶠ k in atTop,∀ d:Model n,
      c0*(1-l)*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
        (iteratedDeriv 2 (fun s=>modifiedScalar α D Bc (β,s)) (v c)/l^2)*
          (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2 - ε*‖d‖^2 ≤
          (J.first k).H d d := by
  obtain ⟨c0,hc0,H⟩ := exists_actual_center_gain (n := n) (M := M)
  refine ⟨c0,hc0,?_⟩
  filter_upwards [H] with l hgain
  intro hl hl1 hmtw u v hu Lv hv hdual α D bminus bplus Bc Bo ho hBc hmono L hLip
    F a c N J q β hq he hQ hβ hder ε hε
  let θ := fun k:ℕ=>1/((k:ℝ)+1)
  have hθpos (k:ℕ) : 0<θ k := by dsimp [θ] <;> positivity
  have hθ : Tendsto θ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨S⟩ := J.exists_diagonal hθpos (P := fun _ _=>True) (fun _=>Eventually.of_forall (fun _=>True.intro))
  obtain ⟨hb,hp,hx,hg⟩ := S.limits J hθ hQ he
  have hlj := S.slope_tendsto hBc hβ hx
  rw [hder] at hlj
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hlj.eventually (Ioo_mem_nhds hl hl1))
  let σ := fun i:ℕ=>i+K
  have hσ : Tendsto σ atTop atTop := tendsto_add_atTop_nat K
  let S1 := S.comp σ hσ
  have hls (i:ℕ) : 0<(J.comp σ hσ).sampleSlope i (S1.ν i) ∧
      (J.comp σ hσ).sampleSlope i (S1.ν i)<1 := hK (i+K) (Nat.le_add_left _ _)
  let CD := S1.center_sequence hu hv hdual hBc hmono hls (hg.comp hσ)
  have hτ : Tendsto (fun k=>1-F.t k) atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_self] using (tendsto_const_nhds.sub F.time :
      Tendsto (fun k=>(1:ℝ)-F.t k) atTop (𝓝 (1-1)))
  have HG := hgain hl hl1 a c u v (modifiedScalar α D Bc) β hv.continuous
    (modifiedScalar_contDiff hBc α D).contDiffAt hder
    (F.b ∘ σ) (fun i=>J.sampleSlope (σ i) (S.ν (σ i))) (fun i=>1-F.t (σ i))
    (F.t ∘ σ) (fun i=>J.sampleCenter (σ i) (S.ν (σ i)))
    (fun i=>graphBaseCoordinate a (J.samplePoint (σ i) (S.ν (σ i))).1)
    (fun i=>graphVelocityCoordinate a (J.samplePoint (σ i) (S.ν (σ i))).1)
    (fun i=>graphProjection (cTransform (modifiedDatum v α D (F.b (σ i)) Bo)) (F.t (σ i))
      (J.samplePoint (σ i) (S.ν (σ i))))
    (fun i=>chartOuterEnvelope (modifiedDatum v α D (F.b (σ i)) Bo) (F.t (σ i)) c)
    CD q hq he (hβ.comp hσ) (hlj.comp hσ) (hτ.comp hσ) (F.time.comp hσ)
    (hx.comp hσ) (hb.comp hσ) (hp.comp hσ)
    (Eventually.of_forall (fun i=>by linarith [(F.prefixTime (σ i)).2])) L
    (Eventually.of_forall (fun i=>hLip _ (Ioo_subset_Icc_self (F.parameter (σ i)))))
    (ε/2) (half_pos hε)
  rw [←map_add_atTop_eq_nat K]
  change ∀ᶠ i in atTop,∀ d:Model n,_≤(J.first (i+K)).H d d
  filter_upwards [HG,(hθ.comp hσ).eventually (gt_mem_nhds (half_pos hε))] with i hi hθi
  intro d
  have Hclose := bilinear_quadratic_close ((S.HClose (σ i)).le.trans hθi.le) d
  have HH := hi d
  change _≤J.sampleH (σ i) (S.ν (σ i)) d d at HH
  nlinarith only [Hclose,HH]

end MaximumCenterLower
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.exists_maximum_center_gain_oai.{u_1} := @OAI.WeakMTWTransport.exists_maximum_center_gain_oai.{u_1}
