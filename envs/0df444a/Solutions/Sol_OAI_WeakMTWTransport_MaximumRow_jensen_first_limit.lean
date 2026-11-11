-- Prove2me | solution 1 for OAI.WeakMTWTransport.MaximumRow.jensen_first_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:42:56.648919+00:00
-- url     : https://prove2.me/submissions/b8d8f322-fe96-41fd-9dcf-35c2e7d99baf

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
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_coordinate_sample_pole_matrix

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

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActiveLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma fixed_simplex_representation {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} {x : E} (hx : x∈convexHull ℝ S) :
    ∃ z : Fin (Module.finrank ℝ E+1) → E, ∃ w : Fin (Module.finrank ℝ E+1) → ℝ,
      (∀ i,z i∈S) ∧ (∀ i,0≤w i) ∧ ∑ i,w i=1 ∧ ∑ i,w i • z i=x := by
  classical
  obtain ⟨m,hm,hN,z,w,hz,hw,hs,hb⟩ := finite_simplex_representation hx
  obtain ⟨r,he⟩ := Nat.exists_eq_add_of_le hN
  rw [he]
  refine ⟨Fin.addCases z (fun _ : Fin r => z ⟨0,hm⟩),
    Fin.addCases w (fun _ : Fin r => 0),?_,?_,?_,?_⟩
  · intro i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simpa only [Fin.addCases_left] using hz j
    · simpa only [Fin.addCases_right] using hz ⟨0,hm⟩
  · intro i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simpa only [Fin.addCases_left] using hw j
    · simp only [Fin.addCases_right,le_refl]
  · simpa only [Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,Finset.sum_const_zero,
      add_zero] using hs
  · simpa only [Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,zero_smul,
      Finset.sum_const_zero,add_zero] using hb

lemma compact_barycentric_limit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {C : Set (E×E)} (hC : IsCompact C)
    {a v : ℕ → E} {a₀ v₀ : E} (ha : Tendsto a atTop (𝓝 a₀))
    (hv : Tendsto v atTop (𝓝 v₀))
    (hrep : ∀ k,v k∈convexHull ℝ {p | (a k,p)∈C}) :
    ∃ z : ℕ → Fin (Module.finrank ℝ E+1) → E,
    ∃ w : ℕ → Fin (Module.finrank ℝ E+1) → ℝ,
    ∃ z₀ : Fin (Module.finrank ℝ E+1) → E,
    ∃ w₀ : Fin (Module.finrank ℝ E+1) → ℝ,
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ k,(∀ i,(a k,z k i)∈C) ∧ (∀ i,0≤w k i) ∧
         ∑ i,w k i=1 ∧ ∑ i,w k i • z k i=v k) ∧
      Tendsto (z ∘ σ) atTop (𝓝 z₀) ∧ Tendsto (w ∘ σ) atTop (𝓝 w₀) ∧
      (∀ i,(a₀,z₀ i)∈C) ∧ (∀ i,0≤w₀ i) ∧ ∑ i,w₀ i=1 ∧ ∑ i,w₀ i • z₀ i=v₀ := by
  classical
  choose z w hz hw hs hb using (fun k=>fixed_simplex_representation (hrep k))
  let d : ℕ → EnvelopeData E (Fin (Module.finrank ℝ E+1)) :=
    fun k=>((a k,z k),(w k,0))
  have hcompact := compact_common_base_configurations
    (ι := Fin (Module.finrank ℝ E+1)) hC 0
  have hd : ∀ k,d k∈{q : EnvelopeData E (Fin (Module.finrank ℝ E+1)) |
      (∀ i,(q.1.1,q.1.2 i)∈C) ∧ (∀ i,0≤q.2.1 i) ∧ ∑ i,q.2.1 i=1 ∧ q.2.2∈Icc 0 0} :=
    fun k=>⟨hz k,hw k,hs k,le_refl _,le_refl _⟩
  obtain ⟨q,hq,σ,hσ,hlim⟩ := hcompact.tendsto_subseq hd
  have ha' : Tendsto (a ∘ σ) atTop (𝓝 q.1.1) := hlim.fst_nhds.fst_nhds
  have hae : q.1.1=a₀ := tendsto_nhds_unique ha' (ha.comp hσ.tendsto_atTop)
  refine ⟨z,w,q.1.2,q.2.1,σ,hσ,(fun k=>⟨hz k,hw k,hs k,hb k⟩),
    hlim.fst_nhds.snd_nhds,hlim.snd_nhds.fst_nhds,?_,hq.2.1,hq.2.2.1,?_⟩
  · simpa only [hae] using hq.1
  · have hsum : Tendsto (fun k=>∑ i,w (σ k) i • z (σ k) i) atTop
        (𝓝 (∑ i,q.2.1 i • q.1.2 i)) := by
      apply tendsto_finsetSum
      intro i _
      exact ((tendsto_pi_nhds.mp hlim.snd_nhds.fst_nhds) i).smul
        ((tendsto_pi_nhds.mp hlim.fst_nhds.snd_nhds) i)
    simp only [hb] at hsum
    exact tendsto_nhds_unique hsum (hv.comp hσ.tendsto_atTop)

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

lemma WeakMTW.graph_points_tendsto (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {q : ℕ → subgradientGraph (n := n) (cTransform v)}
    {q₀ : subgradientGraph (n := n) (cTransform v)}
    (hz : Tendsto (fun k=>graphProjection (cTransform v) t (q k)) atTop
      (𝓝 (graphProjection (cTransform v) t q₀))) :
    Tendsto (fun k=>(q k).1) atTop (𝓝 q₀.1) := by
  have H := (hmtw.graphHomeomorph hv ht ht1).symm.continuous.tendsto
    ((hmtw.graphHomeomorph hv ht ht1) q₀)
  have H' := H.comp hz
  change Tendsto (fun k=>(hmtw.graphHomeomorph hv ht ht1).symm
    ((hmtw.graphHomeomorph hv ht ht1) (q k))) atTop
    (𝓝 ((hmtw.graphHomeomorph hv ht ht1).symm
      ((hmtw.graphHomeomorph hv ht ht1) q₀))) at H'
  simp only [Homeomorph.symm_apply_apply] at H'
  exact continuous_subtype_val.tendsto q₀ |>.comp H'

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

lemma WeakMTW.graph_coordinate_limit_in_chart
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {q : ℕ → subgradientGraph (n := n) (cTransform v)}
    {q₀ : subgradientGraph (n := n) (cTransform v)}
    (hz : Tendsto (fun k=>graphProjection (cTransform v) t (q k)) atTop
      (𝓝 (graphProjection (cTransform v) t q₀)))
    {a : M} (ha : q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    Tendsto (fun k=>graphBaseCoordinate a (q k).1) atTop (𝓝 (graphBaseCoordinate a q₀.1)) ∧
    Tendsto (fun k=>graphVelocityCoordinate a (q k).1) atTop (𝓝 (graphVelocityCoordinate a q₀.1)) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  have hs : q₀.1∈χ.source := (tangent_chart_source_iff _ _).mpr ha
  have H := ((continuousOn_extChartAt _).continuousAt
    ((isOpen_extChartAt_source _).mem_nhds hs)).tendsto.comp
      (hmtw.graph_points_tendsto hv ht ht1 hz)
  exact ⟨H.fst_nhds,H.snd_nhds⟩

lemma WeakMTW.active_barycentric_limit_in_chart
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (q : ℕ → subgradientGraph (n := n) (cTransform v))
    (q₀ : subgradientGraph (n := n) (cTransform v))
    (hz : Tendsto (fun k=>graphProjection (cTransform v) t (q k)) atTop
      (𝓝 (graphProjection (cTransform v) t q₀)))
    {a : M} (ha : q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source)
    {K : Set M} (hK : IsCompact K) (hKa : K⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hqK : ∀ k,(q k).1.1∈K) :
    ∃ pj : ℕ → Fin (Module.finrank ℝ (Model n)+1) → Model n,
    ∃ w : ℕ → Fin (Module.finrank ℝ (Model n)+1) → ℝ,
    ∃ p₀ : Fin (Module.finrank ℝ (Model n)+1) → Model n,
    ∃ w₀ : Fin (Module.finrank ℝ (Model n)+1) → ℝ,
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ k,(∀ i,(graphBaseCoordinate a (q k).1,pj k i)∈activeCoordinates v a K) ∧
        (∀ i,0≤w k i) ∧ ∑ i,w k i=1 ∧ ∑ i,w k i • pj k i=graphVelocityCoordinate a (q k).1) ∧
      Tendsto (pj ∘ σ) atTop (𝓝 p₀) ∧ Tendsto (w ∘ σ) atTop (𝓝 w₀) ∧
      (∀ i,(graphBaseCoordinate a q₀.1,p₀ i)∈activeCoordinates v a K) ∧ (∀ i,0≤w₀ i) ∧
      ∑ i,w₀ i=1 ∧ ∑ i,w₀ i • p₀ i=graphVelocityCoordinate a q₀.1 := by
  obtain ⟨hbase,hvel⟩ := hmtw.graph_coordinate_limit_in_chart hv ht ht1 hz ha
  have hrep : ∀ k,graphVelocityCoordinate a (q k).1∈convexHull ℝ
      {p | (graphBaseCoordinate a (q k).1,p)∈activeCoordinates v a K} := by
    intro k
    let L : TangentSpace 𝓘(ℝ,Model n) (q k).1.1 →ₗ[ℝ] Model n :=
      (tangentCoordChange 𝓘(ℝ,Model n) (q k).1.1 a (q k).1.1).toLinearMap
    have hh : L (q k).1.2 ∈ L '' convexHull ℝ (activeLogs v (q k).1.1) :=
      mem_image_of_mem L (normalSubdifferential_subset_active_hull hv _ (q k).2)
    rw [L.image_convexHull] at hh
    apply convexHull_mono (t := {p | (graphBaseCoordinate a (q k).1,p)∈activeCoordinates v a K}) ?_ hh
    rintro p ⟨r,hr,rfl⟩
    exact ⟨⟨(q k).1.1,r⟩,⟨hr,hqK k⟩,rfl⟩
  exact compact_barycentric_limit (isCompact_active_coordinates hv hK hKa) hbase hvel hrep

lemma WeakMTW.active_barycentric_tail_limit_in_chart
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (q : ℕ → subgradientGraph (n := n) (cTransform v))
    (q₀ : subgradientGraph (n := n) (cTransform v))
    (hz : Tendsto (fun k=>graphProjection (cTransform v) t (q k)) atTop
      (𝓝 (graphProjection (cTransform v) t q₀)))
    {a : M} (ha : q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    ∃ K : Set M,IsCompact K ∧ K⊆(extChartAt 𝓘(ℝ,Model n) a).source ∧
    ∃ pj : ℕ → Fin (Module.finrank ℝ (Model n)+1) → Model n,
    ∃ w : ℕ → Fin (Module.finrank ℝ (Model n)+1) → ℝ,
    ∃ p₀ : Fin (Module.finrank ℝ (Model n)+1) → Model n,
    ∃ w₀ : Fin (Module.finrank ℝ (Model n)+1) → ℝ,
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ k,(∀ i,(graphBaseCoordinate a (q (σ k)).1,pj k i)∈activeCoordinates v a K) ∧
        (∀ i,0≤w k i) ∧ ∑ i,w k i=1 ∧ ∑ i,w k i • pj k i=graphVelocityCoordinate a (q (σ k)).1) ∧
      Tendsto pj atTop (𝓝 p₀) ∧ Tendsto w atTop (𝓝 w₀) ∧
      (∀ i,(graphBaseCoordinate a q₀.1,p₀ i)∈activeCoordinates v a K) ∧ (∀ i,0≤w₀ i) ∧
      ∑ i,w₀ i=1 ∧ ∑ i,w₀ i • p₀ i=graphVelocityCoordinate a q₀.1 := by
  have hbase := (FiberBundle.continuous_proj (Model n)
    (TangentSpace 𝓘(ℝ,Model n))).tendsto q₀.1 |>.comp
      (hmtw.graph_points_tendsto hv ht ht1 hz)
  obtain ⟨K,hK,hKs,N,hN⟩ := compact_in_chart_tail hbase ha
  have hshift : Tendsto (fun k:ℕ=>k+N) atTop atTop := tendsto_add_atTop_nat N
  obtain ⟨pj,w,p₀,w₀,σ,hσ,hs,hp,hw,hact,hn,h1,hb⟩ :=
    hmtw.active_barycentric_limit_in_chart hv ht ht1 (fun k=>q (k+N)) q₀
      (hz.comp hshift) ha hK hKs hN
  exact ⟨K,hK,hKs,pj ∘ σ,w ∘ σ,p₀,w₀,fun k=>σ k+N,
    fun i j hij=>Nat.add_lt_add_right (hσ hij) N,fun k=>hs (σ k),hp,hw,hact,hn,h1,hb⟩

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

omit [Nonempty M] in
lemma movingPrefix_chart_pullback {a c : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source) (f : M → ℝ) :
    (fun q=>f ((extChartAt 𝓘(ℝ,Model n) c).symm (movingPrefixChart a c t b q)))=ᶠ[𝓝 p]
      (fun q=>f (movingPrefix a t b q)) := by
  have hN : ContinuousAt (movingPrefix a t b) p :=
    ((movingPrefix_contMDiffAt (p := p) hb).continuousAt).comp
      (show ContinuousAt (fun q:Model n=>(b,q)) p from by fun_prop)
  filter_upwards [hN.eventually ((isOpen_extChartAt_source (I := 𝓘(ℝ,Model n)) c).mem_nhds hc)]
    with q hq
  exact congrArg f ((extChartAt 𝓘(ℝ,Model n) c).left_inv hq)

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

omit [Nonempty M] in
lemma coordinatePoleMatrix_chart {a c : M} {t : ℝ} {v : M → ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    coordinatePoleMatrix a t v b p=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p-
      fderiv ℝ (fderiv ℝ (fun q=>hopfLax t (cTransform v)
        ((extChartAt 𝓘(ℝ,Model n) c).symm (movingPrefixChart a c t b q)))) p := by
  exact congrArg (fun B=>fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p-B)
    (((movingPrefix_chart_pullback hb hc _).fderiv (𝕜 := ℝ)).fderiv_eq.symm)

omit [Nonempty M] in
lemma coordinateCenterMatrix_chart {a c : M} {t : ℝ} {G : M → ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    coordinateCenterMatrix a t G b p=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p+
      fderiv ℝ (fderiv ℝ (fun q=>G
        ((extChartAt 𝓘(ℝ,Model n) c).symm (movingPrefixChart a c t b q)))) p := by
  exact congrArg (fun B=>fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p+B)
    (((movingPrefix_chart_pullback hb hc _).fderiv (𝕜 := ℝ)).fderiv_eq.symm)

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

lemma WeakMTW.graphCoordinate_prefix_regular (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {a : M} (q : subgradientGraph (n := n) (cTransform v))
    (hq : q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    t • chartFiberInverse a (graphBaseCoordinate a q.1) (graphVelocityCoordinate a q.1)∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (graphBaseCoordinate a q.1)) := by
  exact (congrArg (fun z:TangentBundle 𝓘(ℝ,Model n) M=>t • z.2∈injectivityDomain z.1)
    (graph_coordinate_reconstruction hq)).mpr (hmtw.active_hull_precut hv ht ht1 _ _
      (normalSubdifferential_subset_active_hull hv _ q.2))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ShortEnvelopeJetTest
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma secondJetPullback_apply (j : F →L[ℝ] ℝ) (h : F →L[ℝ] F →L[ℝ] ℝ)
    (m : E →L[ℝ] F) (r : E →L[ℝ] E →L[ℝ] F) (v w : E) :
    secondJetPullback j h m r v w=h (m v) (m w)+j (r v w) := rfl

lemma secondJetPullback_tendsto {ι : Type*} {L : Filter ι}
    {j : ι → F →L[ℝ] ℝ} {h : ι → F →L[ℝ] F →L[ℝ] ℝ}
    {m : ι → E →L[ℝ] F} {r : ι → E →L[ℝ] E →L[ℝ] F}
    {j₀ : F →L[ℝ] ℝ} {h₀ : F →L[ℝ] F →L[ℝ] ℝ}
    {m₀ : E →L[ℝ] F} {r₀ : E →L[ℝ] E →L[ℝ] F}
    (hj : Tendsto j L (𝓝 j₀)) (hh : Tendsto h L (𝓝 h₀))
    (hm : Tendsto m L (𝓝 m₀)) (hr : Tendsto r L (𝓝 r₀)) :
    Tendsto (fun i => secondJetPullback (j i) (h i) (m i) (r i)) L
      (𝓝 (secondJetPullback j₀ h₀ m₀ r₀)) := by
  let : NormedAddCommGroup (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  have hm' := (((ContinuousLinearMap.compL ℝ E F ℝ).flip).continuous.tendsto m₀).comp hm
  have hh' := ((ContinuousLinearMap.compL ℝ E F (F →L[ℝ] ℝ)).continuous₂.tendsto (h₀,m₀)).comp
    (hh.prodMk_nhds hm)
  have hfirst := ((ContinuousLinearMap.compL ℝ E (F →L[ℝ] ℝ) (E →L[ℝ] ℝ)).continuous₂.tendsto
    (((ContinuousLinearMap.compL ℝ E F ℝ).flip) m₀,h₀.comp m₀)).comp (hm'.prodMk_nhds hh')
  have hj' := ((ContinuousLinearMap.compL ℝ E F ℝ).continuous.tendsto j₀).comp hj
  have hsecond := ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] F) (E →L[ℝ] ℝ)).continuous₂.tendsto
    (ContinuousLinearMap.compL ℝ E F ℝ j₀,r₀)).comp (hj'.prodMk_nhds hr)
  exact hfirst.add hsecond

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MovingHessianLimit
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

lemma moving_rough_hessian_limit {ι : Type*} {l : Filter ι}
    {f : F → ℝ} {g : Q → E → F} {b : ι → Q} {x : ι → E}
    {b₀ : Q} {x₀ : E} {j : F →L[ℝ] ℝ} {H : F →L[ℝ] F →L[ℝ] ℝ}
    (hg : ContDiffAt ℝ ∞ (Function.uncurry g) (b₀,x₀))
    (hb : Tendsto b l (𝓝 b₀)) (hx : Tendsto x l (𝓝 x₀))
    (hj : Tendsto (fun i=>fderiv ℝ f (g (b i) (x i))) l (𝓝 j))
    (hH : Tendsto (fun i=>fderiv ℝ (fderiv ℝ f) (g (b i) (x i))) l (𝓝 H))
    (hD : ∀ᶠ i in l,(∀ᶠ y in 𝓝 (g (b i) (x i)),DifferentiableAt ℝ f y) ∧
      DifferentiableAt ℝ (fderiv ℝ f) (g (b i) (x i))) :
    Tendsto (fun i=>fderiv ℝ (fderiv ℝ (fun q=>f (g (b i) q))) (x i)) l
      (𝓝 (secondJetPullback j H (fderiv ℝ (g b₀) x₀)
        (fderiv ℝ (fderiv ℝ (g b₀)) x₀))) := by
  have hbx := hb.prodMk_nhds hx
  have hm := ((ContDiffAt.partial_snd_fderiv hg).continuousAt.tendsto).comp hbx
  have hr := ((ContDiffAt.partial_snd_fderiv_two hg).continuousAt.tendsto).comp hbx
  have ht := secondJetPullback_tendsto hj hH hm hr
  apply ht.congr'
  have hg2 := hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  filter_upwards [hD,hbx.eventually (hg2.eventually (by norm_num))] with i hi hgi
  have hgi' : ContDiffAt ℝ 2 (g (b i)) (x i) :=
    (hgi.comp (x i) (contDiffAt_const.prodMk contDiffAt_id))
  ext d e
  exact (second_fderiv_comp_at hi.1 hi.2 hgi' d e).symm

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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_FirstMatrixLimit
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

lemma secondJetPullback_sum_nonpos
    {j k : F →L[ℝ] ℝ} {A B : F →L[ℝ] F →L[ℝ] ℝ}
    {m : E →L[ℝ] F} {r : E →L[ℝ] E →L[ℝ] F}
    (hj : j+k=0) (hAB : ∀ d:F,A d d+B d d≤0) (e:E) :
    secondJetPullback j A m r e e+secondJetPullback k B m r e e≤0 := by
  have hs := congrArg (fun L:F →L[ℝ] ℝ=>L (r e e)) hj
  simp only [add_apply,zero_apply] at hs
  simp only [secondJetPullback_apply]
  linarith only [hs,hAB (m e)]

lemma first_fixed_prefix_matrix_limit {ι : Type*}
    {W : Q → E → ℝ} {g : Q → E → F} {f h : F → ℝ}
    {b : ℕ → Q} {p : ℕ → E} {b₀ : Q} {p₀ : E}
    {v : ℕ → ι → E} {v₀ : ι → E}
    {jf jh : F →L[ℝ] ℝ} {Af Ah : F →L[ℝ] F →L[ℝ] ℝ}
    (hW : ContDiffAt ℝ ∞ (Function.uncurry W) (b₀,p₀))
    (hg : ContDiffAt ℝ ∞ (Function.uncurry g) (b₀,p₀))
    (hb : Tendsto b atTop (𝓝 b₀)) (hp : Tendsto p atTop (𝓝 p₀))
    (hv : ∀ i,Tendsto (fun k=>v k i) atTop (𝓝 (v₀ i)))
    (hjf : Tendsto (fun k=>fderiv ℝ f (g (b k) (p k))) atTop (𝓝 jf))
    (hjh : Tendsto (fun k=>fderiv ℝ h (g (b k) (p k))) atTop (𝓝 jh))
    (hAf : Tendsto (fun k=>fderiv ℝ (fderiv ℝ f) (g (b k) (p k))) atTop (𝓝 Af))
    (hAh : Tendsto (fun k=>fderiv ℝ (fderiv ℝ h) (g (b k) (p k))) atTop (𝓝 Ah))
    (hDf : ∀ᶠ k in atTop,(∀ᶠ y in 𝓝 (g (b k) (p k)),DifferentiableAt ℝ f y) ∧
      DifferentiableAt ℝ (fderiv ℝ f) (g (b k) (p k)))
    (hDh : ∀ᶠ k in atTop,(∀ᶠ y in 𝓝 (g (b k) (p k)),DifferentiableAt ℝ h y) ∧
      DifferentiableAt ℝ (fderiv ℝ h) (g (b k) (p k)))
    (hgrad : jf+jh=0) (hquad : ∀ d:F,Af d d+Ah d d≤0)
    (hpos : ∀ᶠ k in atTop,∀ d:E,
      0≤(fderiv ℝ (fderiv ℝ (W (b k))) (p k)-
        fderiv ℝ (fderiv ℝ (fun q=>f (g (b k) q))) (p k)) d d)
    (hker : ∀ᶠ k in atTop,∀ i:ι,∀ d:E,
      (fderiv ℝ (fderiv ℝ (W (b k))) (p k)-
        fderiv ℝ (fderiv ℝ (fun q=>f (g (b k) q))) (p k)) (v k i-p k) d=0) :
    ∃ H L : E →L[ℝ] E →L[ℝ] ℝ,
      Tendsto (fun k=>fderiv ℝ (fderiv ℝ (W (b k))) (p k)+
        fderiv ℝ (fderiv ℝ (fun q=>h (g (b k) q))) (p k)) atTop (𝓝 H) ∧
      Tendsto (fun k=>fderiv ℝ (fderiv ℝ (W (b k))) (p k)-
        fderiv ℝ (fderiv ℝ (fun q=>f (g (b k) q))) (p k)) atTop (𝓝 L) ∧
      (∀ d:E,0≤L d d) ∧ (∀ i:ι,∀ d:E,L (v₀ i-p₀) d=0) ∧
      (∀ d:E,H d d≤L d d) := by
  let T := fderiv ℝ (fderiv ℝ (W b₀)) p₀
  let m := fderiv ℝ (g b₀) p₀
  let r := fderiv ℝ (fderiv ℝ (g b₀)) p₀
  let F₀ := secondJetPullback jf Af m r
  let G₀ := secondJetPullback jh Ah m r
  have hT : Tendsto (fun k=>fderiv ℝ (fderiv ℝ (W (b k))) (p k)) atTop (𝓝 T) :=
    ((ContDiffAt.partial_snd_fderiv_two hW).continuousAt.tendsto).comp (hb.prodMk_nhds hp)
  have hF := moving_rough_hessian_limit hg hb hp hjf hAf hDf
  have hG := moving_rough_hessian_limit hg hb hp hjh hAh hDh
  have hH := hT.add hG
  have hL := hT.sub hF
  refine ⟨T+G₀,T-F₀,hH,hL,fun d=>bilinear_limit_nonneg hL hpos d,?_,?_⟩
  · intro i d
    exact bilinear_limit_kernel hL ((hv i).sub hp) (hker.mono (fun k hk=>hk i)) d
  · intro d
    have H := secondJetPullback_sum_nonpos (m := m) (r := r) hgrad hquad d
    change T d d+G₀ d d≤T d d-F₀ d d
    linarith only [H]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ChartFirstMatrix
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

lemma WeakMTW.first_fixed_prefix_limit_in_chart
    (hmtw : WeakMTW (n := n) (M := M)) {v G : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (q : ℕ → subgradientGraph (n := n) (cTransform v))
    (q₀ : subgradientGraph (n := n) (cTransform v))
    (hz : Tendsto (fun k=>graphProjection (cTransform v) t (q k)) atTop
      (𝓝 (graphProjection (cTransform v) t q₀)))
    {a c d : M}
    (ha0 : q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hc : graphProjection (cTransform v) t q₀∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hd : q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) d).source) :
    let χ := extChartAt 𝓘(ℝ,Model n) c
    let F := fun z:Model n=>hopfLax t (cTransform v) (χ.symm z)
    let C := fun z:Model n=>G (χ.symm z)
    let z := fun k=>χ (graphProjection (cTransform v) t (q k))
    let z₀ := χ (graphProjection (cTransform v) t q₀)
    ∀ Af Ac : Model n →L[ℝ] Model n →L[ℝ] ℝ,
      ContinuousAt (fderiv ℝ F) z₀ → ContinuousAt (fderiv ℝ C) z₀ →
      (∀ᶠ z in 𝓝 z₀,DifferentiableAt ℝ F z ∧ DifferentiableAt ℝ C z) →
      Tendsto (fun k=>fderiv ℝ (fderiv ℝ F) (z k)) atTop (𝓝 Af) →
      Tendsto (fun k=>fderiv ℝ (fderiv ℝ C) (z k)) atTop (𝓝 Ac) →
      Tendsto (fun k=>fderiv ℝ F (z k)+fderiv ℝ C (z k)) atTop (𝓝 0) →
      (∀ r:Model n,Af r r+Ac r r≤0) →
      (∀ᶠ k in atTop,DifferentiableAt ℝ (fderiv ℝ F) (z k) ∧
        DifferentiableAt ℝ (fderiv ℝ C) (z k) ∧ DifferentiableAt ℝ
        (fun w:Model n=>extChartAt 𝓘(ℝ,Model n) d
          (hopfPole (n := n) t (cTransform v) (χ.symm w))) (z k)) →
      Nonempty (ChartFixedPrefixLimit a v G t q q₀) := by
  dsimp only
  intro Af Ac hF hC hnear hAf hAc herr hquad hsample
  let χ := extChartAt 𝓘(ℝ,Model n) c
  let F := fun z:Model n=>hopfLax t (cTransform v) (χ.symm z)
  let C := fun z:Model n=>G (χ.symm z)
  let z := fun k=>χ (graphProjection (cTransform v) t (q k))
  let z₀ := χ (graphProjection (cTransform v) t q₀)
  have hzCoord : Tendsto z atTop (𝓝 z₀) :=
    ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds hc)).tendsto.comp hz
  have hjF := hF.tendsto.comp hzCoord
  have hjC := hC.tendsto.comp hzCoord
  have hgrad : fderiv ℝ F z₀+fderiv ℝ C z₀=0 := tendsto_nhds_unique (hjF.add hjC) herr
  obtain ⟨K,hK,hKs,pj,w,pj₀,w₀,σ,hσ,hs,hpj,hw,ha,hn,h1,hbar⟩ :=
    hmtw.active_barycentric_tail_limit_in_chart hv ht ht1 q q₀ hz ha0
  let b := fun k=>graphBaseCoordinate a (q (σ k)).1
  let p := fun k=>graphVelocityCoordinate a (q (σ k)).1
  let b₀ := graphBaseCoordinate a q₀.1
  let p₀ := graphVelocityCoordinate a q₀.1
  have hq := hmtw.graph_points_tendsto hv ht ht1 (hz.comp hσ.tendsto_atTop)
  have hbase := (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).tendsto q₀.1 |>.comp hq
  have hbsource : ∀ᶠ k in atTop,(q (σ k)).1.1∈(extChartAt 𝓘(ℝ,Model n) a).source :=
    hbase.eventually ((isOpen_extChartAt_source _).mem_nhds ha0)
  have hdsource : ∀ᶠ k in atTop,(q (σ k)).1.1∈(extChartAt 𝓘(ℝ,Model n) d).source :=
    hbase.eventually ((isOpen_extChartAt_source _).mem_nhds hd)
  have hzsource : ∀ᶠ k in atTop,graphProjection (cTransform v) t (q (σ k))∈χ.source :=
    (hz.comp hσ.tendsto_atTop).eventually ((isOpen_extChartAt_source _).mem_nhds hc)
  obtain ⟨hb,hp⟩ := hmtw.graph_coordinate_limit_in_chart hv ht ht1 (hz.comp hσ.tendsto_atTop) ha0
  have hb₀ : b₀∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source ha0
  have hp₀ : t • chartFiberInverse a b₀ p₀∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b₀) := by
    exact
      hmtw.graphCoordinate_prefix_regular hv ht ht1 q₀ ha0
  have he₀ : movingPrefix a t b₀ p₀=graphProjection (cTransform v) t q₀ := by
    exact
      movingPrefix_graph_coordinates ha0 t (q := q₀.1)
  have hg := movingPrefixChart_contDiffAt hb₀ (he₀ ▸ hc)
  have henergy := movingPrefixEnergy_contDiffAt hb₀ hp₀
  have he : ∀ᶠ k in atTop,movingPrefix a t (b k) (p k)=
      graphProjection (cTransform v) t (q (σ k)) :=
    hbsource.mono (fun k hk=>movingPrefix_graph_coordinates hk t)
  have hzEq : ∀ᶠ k in atTop,movingPrefixChart a c t (b k) (p k)=z (σ k) :=
    he.mono (fun k hk=>congrArg χ hk)
  have hM : ∀ᶠ k in atTop,
      (∀ r:Model n,0 ≤ coordinatePoleMatrix a t v (b k) (p k) r r) ∧
      (∀ r s:Model n,coordinatePoleMatrix a t v (b k) (p k) r s=
        coordinatePoleMatrix a t v (b k) (p k) s r) ∧
      (∀ i,∀ r:Model n,coordinatePoleMatrix a t v (b k) (p k) (pj k i-p k) r=0) ∧
      (∀ i,chartFiberInverse a (b k) (pj k i)∈
        activeLogs v ((extChartAt 𝓘(ℝ,Model n) a).symm (b k))) ∧
      (∀ i,0<w k i → HasLowerSecondTaylor
        (fun r:Model n=>v (movingNormal a (b k,pj k i+r))+
          ‖chartFiberInverse a (b k) (pj k i+r)‖^2/2) 0
        (w k i • coordinatePoleMatrix a t v (b k) (p k))) := by
    filter_upwards [hbsource,hdsource,hzsource,he,hzEq,hσ.tendsto_atTop.eventually hsample]
      with k hbk hdk hzk hek hzEk hsk
    have hbtk := (extChartAt 𝓘(ℝ,Model n) a).map_source hbk
    have hba : (extChartAt 𝓘(ℝ,Model n) a).symm (b k)=(q (σ k)).1.1 :=
      (extChartAt 𝓘(ℝ,Model n) a).left_inv hbk
    have hact : ∀ i,chartFiberInverse a (b k) (pj k i)∈
        activeLogs v ((extChartAt 𝓘(ℝ,Model n) a).symm (b k)) :=
      fun i=>(mem_active_coordinates hKs ((hs k).1 i)).2.1
    obtain ⟨hpos,hsym,hker,hjet⟩ := hmtw.coordinate_sample_pole_matrix hv ht ht1 hbtk
      (graphCoordinate_normalSubdifferential (q (σ k)) hbk) (hek ▸ hzk) (hba ▸ hdk)
      (show DifferentiableAt ℝ _ (movingPrefixChart a c t (b k) (p k)) from hzEk ▸ hsk.2.2)
    exact ⟨hpos,hsym,fun i=>hker (pj k i) (hact i),hact,
      fun i hi=>hjet _ (pj k) (w k) (hs k).2.1 (hs k).2.2.1 (hs k).2.2.2 hact i hi⟩
  have hL_eq : ∀ᶠ k in atTop,coordinatePoleMatrix a t v (b k) (p k)=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t (b k))) (p k)-
      fderiv ℝ (fderiv ℝ (fun r=>F (movingPrefixChart a c t (b k) r))) (p k) := by
    filter_upwards [hbsource,hzsource,he] with k hbk hzk hek
    exact coordinatePoleMatrix_chart ((extChartAt 𝓘(ℝ,Model n) a).map_source hbk) (hek ▸ hzk)
  have hH_eq : ∀ᶠ k in atTop,coordinateCenterMatrix a t G (b k) (p k)=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t (b k))) (p k)+
      fderiv ℝ (fderiv ℝ (fun r=>C (movingPrefixChart a c t (b k) r))) (p k) := by
    filter_upwards [hbsource,hzsource,he] with k hbk hzk hek
    exact coordinateCenterMatrix_chart ((extChartAt 𝓘(ℝ,Model n) a).map_source hbk) (hek ▸ hzk)
  have hDz : ∀ᶠ k in atTop,
      (∀ᶠ y in 𝓝 (movingPrefixChart a c t (b k) (p k)),DifferentiableAt ℝ F y ∧ DifferentiableAt ℝ C y) ∧
      DifferentiableAt ℝ (fderiv ℝ F) (movingPrefixChart a c t (b k) (p k)) ∧
      DifferentiableAt ℝ (fderiv ℝ C) (movingPrefixChart a c t (b k) (p k)) := by
    filter_upwards [(hzCoord.comp hσ.tendsto_atTop).eventually (eventually_eventually_nhds.mpr hnear),
      hσ.tendsto_atTop.eventually hsample,hzEq] with k hnk hsk hek
    rw [hek]
    exact ⟨hnk,hsk.1,hsk.2.1⟩
  have hpos : ∀ᶠ k in atTop,∀ r:Model n,
      0≤(fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t (b k))) (p k)-
      fderiv ℝ (fderiv ℝ (fun r=>F (movingPrefixChart a c t (b k) r))) (p k)) r r := by
    filter_upwards [hM,hL_eq] with k hk he; rw [←he]; exact hk.1
  have hker : ∀ᶠ k in atTop,∀ i,∀ r:Model n,
      (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t (b k))) (p k)-
      fderiv ℝ (fderiv ℝ (fun r=>F (movingPrefixChart a c t (b k) r))) (p k)) (pj k i-p k) r=0 := by
    filter_upwards [hM,hL_eq] with k hk he; rw [←he]; exact hk.2.2.1
  obtain ⟨H,L,hH,hL,hpositive,hkernel,hupper⟩ := first_fixed_prefix_matrix_limit
    henergy hg hb hp (fun i=>tendsto_pi_nhds.mp hpj i)
    ((hjF.comp hσ.tendsto_atTop).congr' (hzEq.mono (fun k hk=>congrArg (fderiv ℝ F) hk.symm)))
    ((hjC.comp hσ.tendsto_atTop).congr' (hzEq.mono (fun k hk=>congrArg (fderiv ℝ C) hk.symm)))
    ((hAf.comp hσ.tendsto_atTop).congr' (hzEq.mono (fun k hk=>congrArg (fderiv ℝ (fderiv ℝ F)) hk.symm)))
    ((hAc.comp hσ.tendsto_atTop).congr' (hzEq.mono (fun k hk=>congrArg (fderiv ℝ (fderiv ℝ C)) hk.symm)))
    (hDz.mono (fun k hk=>⟨hk.1.mono (fun y hy=>hy.1),hk.2.1⟩))
    (hDz.mono (fun k hk=>⟨hk.1.mono (fun y hy=>hy.2),hk.2.2⟩)) hgrad hquad hpos hker
  have hH' := hH.congr' (hH_eq.mono (fun k hk=>hk.symm))
  have hL' := hL.congr' (hL_eq.mono (fun k hk=>hk.symm))
  refine ⟨⟨σ,hσ,pj,w,pj₀,w₀,H,L,(fun i=>(mem_active_coordinates hKs (ha i)).2.1),hn,h1,hbar,hpj,hw,hH',hL',hpositive,
    fun r s=>bilinear_limit_symm hL' (hM.mono (fun k hk=>hk.2.1)) r s,?_,hupper,?_⟩⟩
  · exact hkernel
  · filter_upwards [hM] with k hk
    exact ⟨(hs k).2.1,(hs k).2.2.1,(hs k).2.2.2,hk.2.2.2.1,hk.2.2.2.2⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_JensenAtFirstLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.jensen_at_first_limit_in_chart (hmtw : WeakMTW (n := n) (M := M))
    {v g : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {a c d : M} {N : Set (Model n)} (J : JensenSamplesAt v g t d c N)
    (hcd : c∈(extChartAt 𝓘(ℝ,Model n) d).source)
    (hF : ContinuousAt (fderiv ℝ (chartOuterEnvelope v t d)) (extChartAt 𝓘(ℝ,Model n) d c))
    (hC : ContinuousAt (fderiv ℝ (chartCenterEnvelope g t d)) (extChartAt 𝓘(ℝ,Model n) d c))
    (hnear : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ,Model n) d c),
      DifferentiableAt ℝ (chartOuterEnvelope v t d) z ∧
      DifferentiableAt ℝ (chartCenterEnvelope g t d) z)
    (ha : hopfPole (n := n) t (cTransform v) c∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let χ := extChartAt 𝓘(ℝ,Model n) d
    let e := hmtw.graphHomeomorph hv ht ht1
    Nonempty (ChartFixedPrefixLimit a v (hopfLax (1-t) g) t
      (fun k=>e.symm (χ.symm (J.z k))) (e.symm c)) := by
  let χ := extChartAt 𝓘(ℝ,Model n) d
  let e := hmtw.graphHomeomorph hv ht ht1
  let q := fun k=>e.symm (χ.symm (J.z k))
  let q₀ := e.symm c
  have hproj : ∀ k,graphProjection (cTransform v) t (q k)=χ.symm (J.z k) :=
    fun k=>e.apply_symm_apply _
  have hproj₀ : graphProjection (cTransform v) t q₀=c := e.apply_symm_apply c
  have hat := χ.map_source hcd
  have hleft : χ.symm (χ c)=c := χ.left_inv hcd
  have hzman : Tendsto (fun k=>χ.symm (J.z k)) atTop (𝓝 c) := by
    have hc : ContinuousAt χ.symm (χ c) := continuousAt_extChartAt_symm'' hat
    have H := hc.tendsto.comp J.points
    rwa [hleft] at H
  have hz : Tendsto (fun k=>graphProjection (cTransform v) t (q k)) atTop
      (𝓝 (graphProjection (cTransform v) t q₀)) := by
    simpa only [hproj,hproj₀] using hzman
  have he : ∀ᶠ k in atTop,χ (graphProjection (cTransform v) t (q k))=J.z k := by
    filter_upwards [J.points.eventually ((isOpen_extChartAt_target d).mem_nhds hat)] with k hk
    rw [hproj]
    exact χ.right_inv hk
  have hc : graphProjection (cTransform v) t q₀∈χ.source :=
    hproj₀ ▸ hcd
  have hpole : q₀.1.1=chartActualPole v t d (χ c) := by
    dsimp only [chartActualPole]
    rw [hleft]
    exact hmtw.graphHomeomorph_inverse_pole hv ht ht1 c
  have hder : ∀ᶠ k in atTop,
      DifferentiableAt ℝ (fderiv ℝ (chartOuterEnvelope v t d))
        (χ (graphProjection (cTransform v) t (q k))) ∧
      DifferentiableAt ℝ (fderiv ℝ (chartCenterEnvelope g t d))
        (χ (graphProjection (cTransform v) t (q k))) ∧
      DifferentiableAt ℝ (fun w:Model n=>extChartAt 𝓘(ℝ,Model n) q₀.1.1
        (chartActualPole v t d w)) (χ (graphProjection (cTransform v) t (q k))) := by
    filter_upwards [he] with k hk
    rw [hk,hpole]
    have H := J.samples k
    exact ⟨H.2.2.2.2.2.2.2.1,H.2.2.2.2.2.2.2.2.1,H.2.2.2.2.2.1.differentiableAt⟩
  have ha0 : q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source := by
    rw [hmtw.graphHomeomorph_inverse_pole hv ht ht1 c]
    exact ha
  apply hmtw.first_fixed_prefix_limit_in_chart hv ht ht1 q q₀ hz ha0 hc
    (mem_extChartAt_source q₀.1.1) J.Af J.Ac
  · simpa only [hproj₀] using hF
  · simpa only [hproj₀] using hC
  · simpa only [hproj₀] using hnear
  · exact J.outerHessians.congr' (he.mono (fun k hk=>congrArg
      (fderiv ℝ (fderiv ℝ (chartOuterEnvelope v t d))) hk.symm))
  · exact J.centerHessians.congr' (he.mono (fun k hk=>congrArg
      (fderiv ℝ (fderiv ℝ (chartCenterEnvelope g t d))) hk.symm))
  · exact J.gradients.congr' (he.mono (fun k hk=>congrArg
      (fun z=>fderiv ℝ (chartOuterEnvelope v t d) z+fderiv ℝ (chartCenterEnvelope g t d) z) hk.symm))
  · exact J.upper
  · exact hder

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
lemma JensenSamplesAt.near_differentiable {v g : M → ℝ} {t : ℝ} {a c : M}
    {N : Set (Model n)} (J : JensenSamplesAt v g t a c N) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ,Model n) a c),
      DifferentiableAt ℝ (chartOuterEnvelope v t a) z ∧
      DifferentiableAt ℝ (chartCenterEnvelope g t a) z := by
  filter_upwards [J.openRegion.mem_nhds J.centerInRegion] with z hz
  exact ⟨J.outerDifferentiable z hz,J.centerDifferentiable z hz⟩

lemma MaximumRow.jensen_first_limit_oai {v : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {z a c : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    (hmtw : WeakMTW (n := n) (M := M)) (hv : Continuous v) (ho : Continuous Bo)
    (ht : 0<t) (ht1 : t<1) {N : Set (Model n)}
    (J : JensenSamplesAt (modifiedDatum v α D b Bo) (modifiedDatum v α D b Bc) t c z N)
    (hc : z∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (ha : R.q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let e := hmtw.graphHomeomorph (continuous_modifiedDatum hv α D b ho) ht ht1
    Nonempty (ChartFixedPrefixLimit a (modifiedDatum v α D b Bo)
      (hopfLax (1-t) (modifiedDatum v α D b Bc)) t
      (fun k=>e.symm ((extChartAt 𝓘(ℝ,Model n) c).symm (J.z k))) R.q) := by
  have hpole : hopfPole (n := n) t (cTransform (modifiedDatum v α D b Bo)) z=R.q.1.1 := by
    rw [←hmtw.graphHomeomorph_inverse_pole (continuous_modifiedDatum hv α D b ho) ht ht1 z,
      R.graph_inverse hmtw hv ho ht ht1]
  have H := hmtw.jensen_at_first_limit_in_chart (continuous_modifiedDatum hv α D b ho) ht ht1 J hc
    (J.outerGradientContinuous.continuousAt (J.openRegion.mem_nhds J.centerInRegion))
    (J.centerGradientContinuous.continuousAt (J.openRegion.mem_nhds J.centerInRegion))
    J.near_differentiable (hpole ▸ ha)
  dsimp only at H ⊢
  rwa [R.graph_inverse hmtw hv ho ht ht1] at H

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.MaximumRow.jensen_first_limit_oai.{u_1} := @OAI.WeakMTWTransport.MaximumRow.jensen_first_limit_oai.{u_1}
