-- Prove2me | solution 1 for OAI.WeakMTWTransport.CenterSequenceData.true_ray_compact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:59.279015+00:00
-- url     : https://prove2.me/submissions/47592dd6-8149-4264-b7b1-d0561865e17a

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
import Definitions.Def_OAIQ232A027
import Theorems.Thm_OAI_WeakMTWTransport_parametric_short_center_pole_limit

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CoordinateScalarSupport
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

lemma coordinateScalarSupport_contDiffAt {a : M} {b p : Model n} {v s : ℝ} {φ : ℝ → ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hs : s≠0)
    (hp : s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hφ : ContDiffAt ℝ ∞ φ v) :
    ContDiffAt ℝ ∞ (coordinateScalarSupport a φ) (((v,s),(b,p)),b) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let Q := ((ℝ×ℝ)×(Model n×Model n))×Model n
  let q : Q := (((v,s),(b,p)),b)
  have hi : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ χ.symm b :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hb)
  have hA : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun q : Q => movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2)) q :=
    (movingNormal_contMDiffAt (q := (b,s • p)) hb).comp
      (f := fun q : Q => (q.1.2.1,q.1.1.2 • q.1.2.2)) q
      (contDiffAt_fst.snd.fst.prodMk (contDiffAt_fst.fst.snd.smul contDiffAt_fst.snd.snd)).contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨χ.symm b,s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ (χ.symm b) p⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hp
  have he : movingNormal a (b,s • p)=riemannianExp (χ.symm b)
      (s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ (χ.symm b) p) := by
    rw [movingNormal_eq hb,map_smul]
  rw [←he] at hc
  have hC : ContDiffAt ℝ ∞ (fun q : Q => cost (χ.symm q.1.2.1)
      (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))) q :=
    (hc.comp (f := fun q : Q => (χ.symm q.1.2.1,
      movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))) q
      ((hi.comp (f := fun q : Q => q.1.2.1) q
        contDiffAt_fst.snd.fst.contMDiffAt).prodMk hA)).contDiffAt
  have hD : ContDiffAt ℝ ∞ (fun q : Q => cost (χ.symm q.2)
      (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))) q :=
    (hc.comp (f := fun q : Q => (χ.symm q.2,
      movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))) q
      ((hi.comp (f := fun q : Q => q.2) q contDiffAt_snd.contMDiffAt).prodMk hA)).contDiffAt
  have hF := (contDiffAt_fst.fst.fst.add (hC.div contDiffAt_fst.fst.snd hs)).sub
    (hD.div contDiffAt_fst.fst.snd hs)
  have hv : q.1.1.1+cost (χ.symm q.1.2.1) (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))/q.1.1.2-
      cost (χ.symm q.2) (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))/q.1.1.2=v := by
    dsimp only [q] <;> ring
  exact (show ContDiffAt ℝ ∞ φ _ from hv.symm ▸ hφ).comp q hF

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ActualEnvelopeJets
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [Nonempty M] [CompleteSpace P] in
lemma jointScalarSupport_contDiffAt {a : M} {b p : Model n} {v s : ℝ}
    {param : P} {Φ : P×ℝ → ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hs : s≠0)
    (hp : s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hΦ : ContDiffAt ℝ ∞ Φ (param,v)) :
    ContDiffAt ℝ ∞ (jointScalarSupport a Φ) ((param,((v,s),(b,p))),b) := by
  have hF := (coordinateScalarSupport_contDiffAt hb hs hp contDiffAt_id).comp
    ((param,((v,s),(b,p))),b) (contDiffAt_fst.snd.prodMk contDiffAt_snd)
  have hpair := contDiffAt_fst.fst.prodMk hF
  exact (show ContDiffAt ℝ ∞ Φ
    (param,coordinateScalarSupport a id (((v,s),(b,p)),b)) from by
      simpa only [coordinateScalarSupport_self,id_eq] using hΦ).comp
        (f := fun q : (P×((ℝ×ℝ)×(Model n×Model n)))×Model n =>
          (q.1.1,coordinateScalarSupport a id (q.1.2,q.2))) _ hpair
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

omit [CompactSpace M] [Nonempty M]
  [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma center_row_parameter_tendsto {c : M} {v : M → ℝ} (hv : Continuous v)
    {γj lj : ℕ → ℝ} {xj rj : ℕ → Model n} {γ l : ℝ} {r : Model n}
    (hγ : Tendsto γj atTop (𝓝 γ)) (hl : Tendsto lj atTop (𝓝 l))
    (hx : Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hr : Tendsto rj atTop (𝓝 r)) :
    Tendsto (fun i=>centerRowParameter c v (γj i) (lj i) (xj i) (rj i)) atTop
      (𝓝 (γ,((v c,(1+l)/2),(extChartAt 𝓘(ℝ,Model n) c c,r)))) := by
  have hb := (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hy := (continuousAt_extChartAt_symm'' hb).tendsto.comp hx
  rw [(extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)] at hy
  exact hγ.prodMk_nhds (((hv.tendsto c).comp hy).prodMk_nhds
    ((tendsto_const_nhds.add hl).div_const 2) |>.prodMk_nhds (hx.prodMk_nhds hr))

omit [Nonempty M] in
lemma center_support_family_subseq {c : M} {u v : M → ℝ} {Φ : ℝ×ℝ → ℝ}
    {γj lj τj : ℕ → ℝ} {xj : ℕ → Model n} {zj : ℕ → M}
    (R : ∀ i,TrueCenterRow c u v (fun s=>Φ (γj i,s)) (xj i) (zj i) (τj i) (lj i))
    (hx : Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ r : Model n,
      (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c ∧
      Tendsto (fun i=>(R (σ i)).r) atTop (𝓝 r) :=
  minimizing_coordinates_tail_subseq hx (fun i=>(R i).chart) (fun i=>(R i).minimizing)

omit [Nonempty M] in
lemma center_limit_support_smooth {c : M} {r : Model n} {γ l : ℝ} {v : M → ℝ}
    {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiffAt ℝ ∞ Φ (γ,v c))
    (hr : (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c)
    (hl : 0<l) (hl1 : l<1) :
    ContDiffAt ℝ ∞ (jointScalarSupport c Φ)
      ((γ,((v c,(1+l)/2),(extChartAt 𝓘(ℝ,Model n) c c,r))),extChartAt 𝓘(ℝ,Model n) c c) := by
  have hb := (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hp : ((1+l)/2) • chartFiberInverse c (extChartAt 𝓘(ℝ,Model n) c c) r∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) c).symm (extChartAt 𝓘(ℝ,Model n) c c)) := by
    rw [chartFiberInverse_at_center,(extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)]
    exact contracted_minimizer_mem_injectivityDomain hr (by linarith) (by linarith)
  exact jointScalarSupport_contDiffAt hb (by linarith) hp hΦ

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

lemma reverse_minimizer_eq {a c:M}
    {r:TangentSpace 𝓘(ℝ,Model n) c} {q:TangentSpace 𝓘(ℝ,Model n) a}
    (hr:r∈injectivityDomain c) (hq:q∈minimizingVectors a)
    (ha:riemannianExp c r=a) (hc:riemannianExp a q=c) :
    reverseRay (⟨c,r⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ := by
  let z:TangentBundle 𝓘(ℝ,Model n) M:=⟨c,r⟩
  have hb:(reverseRay z).1=a:=(reverseRay_base z).trans ha
  have hR:=reverseRay_regular (z:=z) hr
  have hE:=reverseRay_endpoint z
  generalize hw:reverseRay z=w
  rw [hw] at hb hR hE
  rcases w with ⟨b,p⟩
  change b=a at hb
  subst b
  have he:=riemannianExp_interior_unique hR hq (hE.trans hc.symm)
  exact congrArg (fun v:TangentSpace 𝓘(ℝ,Model n) a=>(⟨a,v⟩:TangentBundle 𝓘(ℝ,Model n) M)) he

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterPoleStationary
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
section CenterPoleStationary
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma CenterSequenceData.pole {a c:M} {u v:M → ℝ} {Φ:ℝ×ℝ → ℝ} {γ l:ℝ}
    (hv:Continuous v) (hΦ:ContDiffAt ℝ ∞ Φ (γ,v c))
    (hder:deriv (fun s=>Φ (γ,s)) (v c)=l) (hl:0 < l) (hl1:l < 1)
    {γj lj τj tj:ℕ → ℝ} {xj bj qj:ℕ → Model n} {zj:ℕ → M}
    {F:ℕ → Model n → ℝ}
    (D:CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F)
    {r:Model n} (hr:(show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c)
    (hγ:Tendsto γj atTop (𝓝 γ)) (hlm:Tendsto lj atTop (𝓝 l))
    (hτ:Tendsto τj atTop (𝓝 0)) (ht:Tendsto tj atTop (𝓝 1))
    (hx:Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hrr:Tendsto (fun i=>(D.row i).r) atTop (𝓝 r))
    (hτpos:∀ᶠ i in atTop,0 < τj i) (L:ℝ≥0)
    (hLip:∀ᶠ i in atTop,LipschitzWith L (fun y=>Φ (γj i,v y))) :
    a=riemannianExp c (l • r) := by
  let p := (γ,((v c,(1+l)/2),(extChartAt 𝓘(ℝ,Model n) c c,r)))
  let pj := fun i=>centerRowParameter c v (γj i) (lj i) (xj i) (D.row i).r
  let ψ := jointScalarSupport (n := n) c Φ
  have hp : Tendsto pj atTop (𝓝 p) := center_row_parameter_tendsto hv hγ hlm hx hrr
  have hψ : ContDiffAt ℝ ∞ ψ (p,extChartAt 𝓘(ℝ,Model n) c c) :=
    center_limit_support_smooth hΦ hr hl hl1
  have hs : ((1+l)/2)≠0 := by linarith
  have hr' := contracted_minimizer_mem_injectivityDomain hr (t := (1+l)/2)
    (by linarith) (by linarith)
  have hc := (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hφinf : ContDiffAt ℝ ∞ (fun s=>Φ (γ,s)) (v c) :=
    hΦ.comp (v c) (contDiffAt_const.prodMk contDiffAt_id)
  have hφ2 : ContDiffAt ℝ 2 (fun s=>Φ (γ,s)) (v c) :=
    hφinf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hφ : HasDerivAt (fun s=>Φ (γ,s)) l (v c) := by
    rw [←hder]
    exact (hφinf.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt
  have hforward (i : ℕ) : parametricShortForward c ψ ((pj i,τj i),xj i)=
      extChartAt 𝓘(ℝ,Model n) c (zj i) := (D.row i).forward
  have hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤Φ (γj i,v ((extChartAt 𝓘(ℝ,Model n) c).symm w)) :=
    Eventually.of_forall (fun i=>(D.row i).below)
  have htouch : ∀ᶠ i in atTop,
      Φ (γj i,v ((extChartAt 𝓘(ℝ,Model n) c).symm (xj i)))=ψ (pj i,xj i) :=
    Eventually.of_forall (fun i=>(D.row i).touching.symm)
  have ha : Tendsto (fun i=>(extChartAt 𝓘(ℝ,Model n) a).symm (bj i)) atTop (𝓝 a) := by
    have hb0 := (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
    have hy := (continuousAt_extChartAt_symm'' hb0).tendsto.comp hb
    rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)] at hy
    exact hy
  have hd : ∀ᶠ i in atTop,DifferentiableAt ℝ
      (fun w=>hopfLax (τj i) (fun y=>Φ (γj i,v y)) ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (parametricShortForward c ψ ((pj i,τj i),xj i)) := by
    filter_upwards [D.derivative] with i hi
    rw [hforward]
    exact hi.1.self_of_nhds
  have herr := D.gradient.congr' (Eventually.of_forall (fun i=>by rw [←hforward i]))
  have hback : ∀ᶠ i in atTop,coordinateBackward c (tj i,
      parametricShortForward c ψ ((pj i,τj i),xj i),
      fderiv ℝ (F i) (parametricShortForward c ψ ((pj i,τj i),xj i)))=
        (extChartAt 𝓘(ℝ,Model n) a).symm (bj i) := by
    simpa only [hforward] using D.backward
  have hstationary : a=riemannianExp c (l • r) :=
    parametric_short_center_pole_limit L hψ hs hr' hφ rfl hp hx ht hτ ha hτpos hLip
      hbelow htouch hd herr hback
  exact hstationary

end CenterPoleStationary
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

section
variable [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma modified_reverseRay_tendsto {c:M} {b r:ℕ → Model n} {l:ℕ → ℝ} {r0:Model n} {l0:ℝ}
    (hb:Tendsto b atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hr:Tendsto r atTop (𝓝 r0)) (hl:Tendsto l atTop (𝓝 l0)) :
    Tendsto (fun k=>reverseRay (tangentScale (l k) (chartRay c (b k) (r k)))) atTop
      (𝓝 (reverseRay (⟨c,l0 • r0⟩:TangentBundle 𝓘(ℝ,Model n) M))) := by
  exact continuous_reverseRay.continuousAt.tendsto.comp
    (contMDiff_tangentScale.continuous.continuousAt.tendsto.comp
      (hl.prodMk_nhds (chartRay_tendsto hb hr)))

end

end CenterRayLimit
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterTrueRayCompact
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
section CenterTrueRayCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma CenterSequenceData.true_ray_compact_oai {a c:M} {u v:M → ℝ} {Φ:ℝ×ℝ → ℝ} {γ l:ℝ}
    (hv:Continuous v) (hΦ:ContDiffAt ℝ ∞ Φ (γ,v c))
    (hder:deriv (fun s=>Φ (γ,s)) (v c)=l) (hl:0 < l) (hl1:l < 1)
    {γj lj τj tj:ℕ → ℝ} {xj bj qj:ℕ → Model n} {zj:ℕ → M}
    {F:ℕ → Model n → ℝ}
    (D:CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F)
    {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a)
    (he:riemannianExp a q=c)
    (hγ:Tendsto γj atTop (𝓝 γ)) (hlm:Tendsto lj atTop (𝓝 l))
    (hτ:Tendsto τj atTop (𝓝 0)) (ht:Tendsto tj atTop (𝓝 1))
    (hx:Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hτpos:∀ᶠ i in atTop,0 < τj i) (L:ℝ≥0)
    (hLip:∀ᶠ i in atTop,LipschitzWith L (fun y=>Φ (γj i,v y))) :
    ∃σ:ℕ → ℕ,StrictMono σ ∧ ∃r:Model n,
      (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c ∧
      Tendsto (fun i=>(D.row (σ i)).r) atTop (𝓝 r) ∧
      Tendsto (fun i=>reverseRay (tangentScale (lj (σ i))
        (chartRay c (xj (σ i)) (D.row (σ i)).r))) atTop
        (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) := by
  obtain ⟨σ,hσ,r,hr,hrr⟩:=center_support_family_subseq D.row hx
  have HP: a=riemannianExp c (l • r):=
    (D.comp σ hσ.tendsto_atTop).pole hv hΦ hder hl hl1 hr
      (hγ.comp hσ.tendsto_atTop) (hlm.comp hσ.tendsto_atTop)
      (hτ.comp hσ.tendsto_atTop) (ht.comp hσ.tendsto_atTop)
      (hx.comp hσ.tendsto_atTop) (hb.comp hσ.tendsto_atTop) hrr
      (hσ.tendsto_atTop.eventually hτpos) L (hσ.tendsto_atTop.eventually hLip)
  have HE:=reverse_minimizer_eq (contracted_minimizer_mem_injectivityDomain hr hl hl1)
    hq HP.symm he
  refine ⟨σ,hσ,r,hr,hrr,?_⟩
  have HT:=modified_reverseRay_tendsto (hx.comp hσ.tendsto_atTop) hrr
    (hlm.comp hσ.tendsto_atTop)
  have HE' : reverseRay (⟨c,l • r⟩ : TangentBundle 𝓘(ℝ,Model n) M) =
      (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M) := by exact HE
  rw [HE'] at HT
  exact HT

end CenterTrueRayCompact
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.CenterSequenceData.true_ray_compact_oai.{u_1} := @OAI.WeakMTWTransport.CenterSequenceData.true_ray_compact_oai.{u_1}
