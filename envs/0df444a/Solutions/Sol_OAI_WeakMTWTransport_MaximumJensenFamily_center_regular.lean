-- Prove2me | solution 1 for OAI.WeakMTWTransport.MaximumJensenFamily.center_regular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:42:55.284976+00:00
-- url     : https://prove2.me/submissions/8d7d56bf-6989-4d4b-a949-fbccd0959f20

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
import Theorems.Thm_OAI_WeakMTWTransport_CenterSequenceData_regular_compact

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumCenterRegular
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
section MaximumCenterRegular
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
lemma MaximumJensenFamily.center_regular_oai
    {u v : M → ℝ} (hu : Continuous u) {Lv : ℝ≥0} (hv : LipschitzWith Lv v)
    (hdual : IsCostDualPair u v)
    {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ} {ho : Continuous Bo}
    (hBc : ContDiff ℝ ∞ Bc)
    (hmono : ∀ b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s)))
    (L : ℝ≥0) (hLip : ∀ b∈Icc bminus bplus,LipschitzWith L (modifiedDatum v α D b Bc))
    {hmtw : WeakMTW (n := n) (M := M)}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c:M} {N:Set (Model n)}
    (J : MaximumJensenFamily hmtw hv.continuous ho F a c N)
    {q:Model n} {β l:ℝ}
    (hq : (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a)
    (he : riemannianExp a q=c)
    (hQ : Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    (hβ : Tendsto F.b atTop (𝓝 β))
    (hder : deriv (fun s=>modifiedScalar α D Bc (β,s)) (v c)=l)
    (hl:0<l) (hl1:l<1) :
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a := by
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
  exact CD.regular_compact hv.continuous (modifiedScalar_contDiff hBc α D).contDiffAt
    hder hl hl1 hq he (hβ.comp hσ) (hlj.comp hσ) (hτ.comp hσ)
    (F.time.comp hσ) (hx.comp hσ) (hb.comp hσ)
    (Eventually.of_forall (fun i=>by change 0 < 1-F.t (σ i); linarith [(F.prefixTime (σ i)).2])) L
    (Eventually.of_forall (fun i=>hLip _ (Ioo_subset_Icc_self (F.parameter (σ i)))))

end MaximumCenterRegular
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.MaximumJensenFamily.center_regular_oai.{u_1} := @OAI.WeakMTWTransport.MaximumJensenFamily.center_regular_oai.{u_1}
