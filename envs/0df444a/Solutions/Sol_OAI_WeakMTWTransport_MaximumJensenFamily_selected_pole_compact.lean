-- Prove2me | solution 1 for OAI.WeakMTWTransport.MaximumJensenFamily.selected_pole_compact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:42:25.299462+00:00
-- url     : https://prove2.me/submissions/8797b841-cc6e-491f-ad3a-0611fa8c7557

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
import Theorems.Thm_OAI_WeakMTWTransport_MaximumJensenFamily_active_outward_compact
import Theorems.Thm_OAI_WeakMTWTransport_MaximumJensenFamily_eventual_outward
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_coordinate_sample_pole_matrix
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_modified_outer_neighborhood

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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_EigenOrder
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
  [CompleteSpace E]

lemma bilinearOperator_symmetric {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ v w:E, B v w=B w v) : (bilinearOperator B).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (bilinearOperator B v) w=inner ℝ v (bilinearOperator B w)
  calc
    _=B v w := bilinearOperator_inner B v w
    _=B w v := hB v w
    _=inner ℝ (bilinearOperator B w) v := (bilinearOperator_inner B w v).symm
    _=inner ℝ v (bilinearOperator B w) := real_inner_comm _ _

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearCompact
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
section BilinearCompact
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma symmetric_bilinear_norm_bound {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:∀d e,B d e=B e d) {C:ℝ} (hC:0≤C)
    (hbound:∀d,|B d d|≤C*‖d‖^2) : ‖B‖≤C := by
  let T:=bilinearOperator B
  have hT:T.IsSymmetric := bilinearOperator_symmetric hB
  have hn:‖T‖≤C := by
    rw [T.norm_eq_iSup_rayleighQuotient hT]
    apply ciSup_le
    intro d
    by_cases hd:d=0
    · simpa [hd,ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply] using hC
    · have hp:0<‖d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
      simp only [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply]
      simp only [T,bilinearOperator_inner,RCLike.re_to_real]
      rw [abs_div,abs_of_pos hp]
      apply (div_le_iff₀ hp).mpr
      exact hbound d
  apply B.opNorm_le_bound hC
  intro d
  apply (B d).opNorm_le_bound (mul_nonneg hC (norm_nonneg d))
  intro e
  calc
    ‖B d e‖ = ‖inner ℝ (T d) e‖ := by simp only [T,bilinearOperator_inner]
    _ ≤ ‖T d‖*‖e‖ := norm_inner_le_norm _ _
    _ ≤ (‖T‖*‖d‖)*‖e‖ := mul_le_mul_of_nonneg_right (T.le_opNorm d) (norm_nonneg e)
    _ ≤ (C*‖d‖)*‖e‖ := by gcongr

attribute [local instance] OAI.WeakMTWTransport.bilinearCompactDualGroup
attribute [local instance] OAI.WeakMTWTransport.bilinearCompactDualSpace
attribute [local instance] OAI.WeakMTWTransport.bilinearCompactGroup
attribute [local instance] OAI.WeakMTWTransport.bilinearCompactSpace
omit [CompleteSpace E] in
lemma exists_bilinear_limit [FiniteDimensional ℝ E]
    {Bj:ℕ → E →L[ℝ] E →L[ℝ] ℝ} {C:ℝ}
    (hb:∀ᶠ j in atTop,‖Bj j‖≤C) :
    ∃B:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧ Tendsto (Bj ∘ σ) atTop (𝓝 B) := by
  let : FiniteDimensional ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
  let : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
  obtain ⟨N,hN⟩:=eventually_atTop.mp hb
  have H : IsCompact (Metric.closedBall (0:E →L[ℝ] E →L[ℝ] ℝ) C) := isCompact_closedBall _ _
  obtain ⟨B,hB,σ,hσ,hlim⟩:=H.tendsto_subseq (x := fun j => Bj (j+N)) (fun j=>by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hN (j+N) (Nat.le_add_left _ _))
  exact ⟨B,fun j=>σ j+N,fun i j hij=>Nat.add_lt_add_right (hσ hij) N,hlim⟩
end BilinearCompact
end WeakMTWTransport

end
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumOuterBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section MaximumOuterBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma MaximumJensenFamily.outer_bound
    {hmtw:WeakMTW (n := n) (M := M)}
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {x0:M}
    {uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv:uv∈densityDualClass (metricVolume n) lam cap x0)
    {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} (ho:ContDiff ℝ ∞ Bo)
    {F:MaximumFamily (n := n) uv.2 α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)}
    (J:MaximumJensenFamily hmtw uv.2.continuous ho.continuous F a c N)
    {β:ℝ} (hb:Tendsto F.b atTop (𝓝 β))
    (hbcoord:Tendsto (fun k=>graphBaseCoordinate a (F.row k).q.1) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (i:ℕ → Fin (Module.finrank ℝ (Model n)+1)) {r:Model n}
    (hr:Tendsto (fun k=>(J.first k).pj₀ (i k)) atTop (𝓝 r))
    {mstar:ℝ} (hmstar:0 < mstar) (hm:∀ᶠ k in atTop,mstar ≤ (J.first k).w₀ (i k))
    (hmono:∀k,StrictMono (fun s=>modifiedScalar α D Bo (F.b k,s)))
    (hmono0:StrictMono (fun s=>modifiedScalar α D Bo (β,s)))
    (hslope:1 < deriv (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a r)))
    (hcurve:iteratedDeriv 2 (fun s=>modifiedScalar α D Bo (β,s))
      (uv.2 (riemannianExp a r)) < 0) :
    ∃C≥0,∀ᶠ k in atTop,∀d:Model n,(J.first k).L d d ≤ C*‖d‖^2 := by
  have hactive:(show TangentSpace 𝓘(ℝ,Model n) a from r)∈
      activeLogs (modifiedDatum uv.2 α D β Bo) a :=
    modified_active_coordinates_limit uv.2.continuous ho.continuous hb hbcoord hr
      (Eventually.of_forall (fun k=>(extChartAt 𝓘(ℝ,Model n) a).map_source (J.poleSource k)))
      (Eventually.of_forall (fun k=>(J.first k).activeLimit (i k)))
  obtain ⟨U,hU,C,hC,HC⟩:=hmtw.modified_outer_neighborhood hlam hcap huv
    (modifiedScalar_contDiff ho α D) hmono0 hactive hslope hcurve
  have hlim:Tendsto (fun k=>((graphBaseCoordinate a (F.row k).q.1,(J.first k).pj₀ (i k)),F.b k))
      atTop (𝓝 ((extChartAt 𝓘(ℝ,Model n) a a,r),β)) :=
    (hbcoord.prodMk_nhds hr).prodMk_nhds hb
  have hnear:∀ᶠ k in atTop,U∈𝓝 ((graphBaseCoordinate a (F.row k).q.1,(J.first k).pj₀ (i k)),F.b k) :=
    hlim.eventually (eventually_eventually_nhds.mpr hU)
  refine ⟨C/mstar,div_nonneg hC hmstar.le,?_⟩
  filter_upwards [hnear,hm] with k hUk hmk
  have hσ:=(J.first k).strictMono.tendsto_atTop
  obtain ⟨hq,hb',hp'⟩:=(F.row k).jensen_graph_limit hmtw uv.2.continuous ho.continuous
    (F.prefixTime k).1 (F.prefixTime k).2 (J.sample k) (J.endpointSource k) (J.poleSource k)
  have hlj:Tendsto (fun j=>((graphBaseCoordinate a (J.samplePoint k j).1,
      (J.first k).pj j (i k)),F.b k)) atTop
      (𝓝 ((graphBaseCoordinate a (F.row k).q.1,(J.first k).pj₀ (i k)),F.b k)) :=
    ((hb'.comp hσ).prodMk_nhds (tendsto_pi_nhds.mp (J.first k).pjLimit (i k))).prodMk_nhds tendsto_const_nhds
  have hw:Tendsto (fun j=>(J.first k).w j (i k)) atTop (𝓝 ((J.first k).w₀ (i k))) :=
    tendsto_pi_nhds.mp (J.first k).wLimit (i k)
  have hwpos:∀ᶠ j in atTop,0 < (J.first k).w j (i k) :=
    hw.eventually (lt_mem_nhds (hmstar.trans_le hmk))
  have H:∀ᶠ j in atTop,∀d:Model n,(J.first k).w j (i k)*J.sampleL k j d d ≤ C*‖d‖^2 := by
    filter_upwards [hlj.eventually hUk,hwpos,J.sample_pole_positive k,(J.first k).samples]
      with j hj hwj hpos hjets
    intro d
    exact HC _ hj (hmono k) ((J.first k).w j (i k) • J.sampleL k j)
      (fun e=>by exact mul_nonneg hwj.le (hpos e)) (hjets.2.2.2.2 (i k) hwj) d
  intro d
  have hld:Tendsto (fun j=>J.sampleL k j d d) atTop (𝓝 ((J.first k).L d d)) :=
    ((show Continuous (fun B:Model n →L[ℝ] Model n →L[ℝ] ℝ=>B d d) from
      (continuous_id.clm_apply continuous_const).clm_apply continuous_const).tendsto _).comp
        (J.first k).LLimit
  have HQ:(J.first k).w₀ (i k)*(J.first k).L d d ≤ C*‖d‖^2 :=
    le_of_tendsto (hw.mul hld) (H.mono (fun j hj=>hj d))
  have Hstar:mstar*(J.first k).L d d ≤ C*‖d‖^2 :=
    (mul_le_mul_of_nonneg_right hmk ((J.first k).positive d)).trans HQ
  calc
    (J.first k).L d d ≤ (C*‖d‖^2)/mstar := (le_div_iff₀ hmstar).mpr (by nlinarith only [Hstar])
    _ = C/mstar*‖d‖^2 := by ring

end MaximumOuterBound
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

local instance poleCompactDualGroup_r8d8d6a_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance poleCompactDualSpace_r8d8d6a_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance poleCompactBilinearGroup_r8d8d6a_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance poleCompactBilinearSpace_r8d8d6a_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma MaximumJensenFamily.pole_compact (J:MaximumJensenFamily hmtw hv ho F a c N)
    {U:ℝ} (hU:0 ≤ U) (hL:∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ U*‖d‖^2) :
    ∃L:Model n →L[ℝ] Model n →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (fun k=>(J.first (σ k)).L) atTop (𝓝 L) := by
  apply exists_bilinear_limit (Bj:=fun k=>(J.first k).L) (C:=U)
  filter_upwards [hL] with k hk
  apply symmetric_bilinear_norm_bound (J.first k).symmetric hU
  intro d
  rw [abs_of_nonneg ((J.first k).positive d)]
  exact hk d

end MaximumPoleCompact
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumSelectionCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section MaximumSelectionCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumJensenFamily.selected_pole_compact_oai
    {hmtw:WeakMTW (n:=n) (M:=M)} {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {x0:M}
    {uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv:uv∈densityDualClass (metricVolume n) lam cap x0)
    {α D bminus bplus H:ℝ} {Bc Bo:ℝ → ℝ} (ho:ContDiff ℝ ∞ Bo)
    {F:MaximumFamily (n:=n) uv.2 α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)}
    (J:MaximumJensenFamily hmtw uv.2.continuous ho.continuous F a c N)
    (hd:IsCostDualPair (uv.1:M → ℝ) uv.2)
    (hm:0 ≤ bminus) (hp:0 < bplus) (hprofiles:∀s,Bc s ≤ Bo s)
    (hob:∀s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb:∀s,-1 ≤ Bc s ∧ Bc s ≤ 1)
    (hright:∀s,3/4 ≤ s → Bc s ≤ 0)
    {q:Model n} {β:ℝ} (hβ:Tendsto F.b atTop (𝓝 β))
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {A C:ℝ} (hA:0 < A) (hC:C < 0)
    (hH:∀ε:ℝ,0 < ε → ∀ᶠ k in atTop,∀d:Model n,
      A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
      C*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤ (J.first k).H d d)
    {eta delta zeta a0:ℝ} (hD:0 < D) (ha0:0 < a0) (hqa:2*(-C)*a0*D ≤ A)
    (heta:eta ≤ 1/128) (hdelta:delta ≤ zeta) (hdeltaEta:delta ≤ eta) (hzeta:zeta ≤ 1/16)
    (hleft:∀s,s < 1-eta → 1 ≤ Bo s)
    (herror:∀k,2*(H+2)*F.b k ≤ zeta*D)
    (hosc:∀k,sectionOscillation uv.1 uv.2 (F.row k).q.1.1 ((H+2)*F.b k) ≤ (1+delta)*D)
    (hmono:∀b∈Icc bminus bplus,StrictMono (fun s=>modifiedScalar α D Bo (b,s)))
    (hmargin:∀s:ℝ,-2*eta ≤ s → s ≤ 1-eta →
      Bo s ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096) →
      1 < deriv (fun z=>modifiedScalar α D Bo (β,z)) (α+D*s) ∧
      iteratedDeriv 2 (fun z=>modifiedScalar α D Bo (β,z)) (α+D*s)<0) :
    ∃σ:ℕ → ℕ,StrictMono σ ∧
    ∃r:Fin (Module.finrank ℝ (Model n)+1) → Model n,
    ∃m:Fin (Module.finrank ℝ (Model n)+1) → ℝ,
    ∃L:Model n →L[ℝ] Model n →L[ℝ] ℝ,∃CL:ℝ,0 ≤ CL ∧
    ∃i:Fin (Module.finrank ℝ (Model n)+1),
      Tendsto (fun k=>(J.first (σ k)).pj₀) atTop (𝓝 r) ∧
      Tendsto (fun k=>(J.first (σ k)).w₀) atTop (𝓝 m) ∧
      Tendsto (fun k=>(J.first (σ k)).L) atTop (𝓝 L) ∧
      (∀ᶠ k in atTop,∀d,(J.first (σ k)).L d d ≤ CL*‖d‖^2) ∧
      (∀j,(show TangentSpace 𝓘(ℝ,Model n) a from r j)∈minimizingVectors a) ∧
      (∀j,0 ≤ m j) ∧ ∑j,m j=1 ∧ ∑j,m j • r j=q ∧
      (1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ)) ≤ m i ∧
      -2*eta ≤ (uv.2 (riemannianExp a (r i))-α)/D ∧
      (uv.2 (riemannianExp a (r i))-α)/D ≤ 1-eta ∧
      Bo ((uv.2 (riemannianExp a (r i))-α)/D) ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096) ∧
      ∃e:TangentSpace 𝓘(ℝ,Model n) a,∃d:ℝ,‖e‖=1 ∧ 0 < d ∧
        (show TangentSpace 𝓘(ℝ,Model n) a from r i)=
          (show TangentSpace 𝓘(ℝ,Model n) a from q)+d • e ∧
        0 < inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e ∧
        a0*D ≤ (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) e)^2 ∧
        ‖show TangentSpace 𝓘(ℝ,Model n) a from r i‖^2-
          ‖show TangentSpace 𝓘(ℝ,Model n) a from q‖^2 ≤ (3+9/(4*a0))*D := by
  have hsel:=J.eventual_outward uv.1.continuous hd hm hp hprofiles hob hcb hright hQ hA hC
    hH hD ha0 hqa heta hdelta hdeltaEta hzeta hleft herror hosc
  let μ:ℝ:=(1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ))
  let ν:ℝ:=(1/4096)/(8*(Module.finrank ℝ (Model n)+1:ℝ))
  have hμ:0 < μ:=by dsimp [μ] <;> positivity
  have hν:0 < ν:=by dsimp [ν] <;> positivity
  obtain ⟨σ,hσ,r,m,i,hr,hm',ha,hmn,hmt,hbar,hmi,hmi',hs,hs',hcapO,e,d,he,hd',hri,hpe,hpD,hmom,hdmax,hgap⟩:=
    J.active_outward_compact hβ hQ hμ hν ha0 hD (by
      filter_upwards [hsel] with k hk
      obtain ⟨e,i,d,he,hpe,hpD,hd,hri,hmi,hmom,hdmax,hs,hs',hcapO⟩:=hk
      refine ⟨i,e,d,he,hpe,hpD,hd,hri,hmi,?_,hdmax,hs,hs',hcapO⟩
      dsimp only [ν]
      convert! hmom using 1
      all_goals try with_reducible_and_instances rfl
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring)
  have hβmem:β∈Icc bminus bplus:=isClosed_Icc.mem_of_tendsto hβ
    (Eventually.of_forall (fun k=>Ioo_subset_Icc_self (F.parameter k)))
  have hz:α+D*((uv.2 (riemannianExp a (r i))-α)/D)=uv.2 (riemannianExp a (r i)):=by
    field_simp [hD.ne']
    ring
  have hmar:=hmargin _ hs hs' hcapO
  rw [hz] at hmar
  let J':=J.comp σ hσ.tendsto_atTop
  obtain ⟨CL,hCL,HCL⟩:=J'.outer_bound hlam hcap huv ho (hβ.comp hσ.tendsto_atTop)
    ((F.limit_coordinates hQ).1.comp hσ.tendsto_atTop) (fun _=>i)
    (tendsto_pi_nhds.mp hr i) hμ hmi'
    (fun k=>hmono _ (Ioo_subset_Icc_self (F.parameter (σ k)))) (hmono β hβmem) hmar.1 hmar.2
  obtain ⟨L,τ,hτ,hL⟩:=J'.pole_compact hCL HCL
  refine ⟨σ ∘ τ,hσ.comp hτ,r,m,L,CL,hCL,i,hr.comp hτ.tendsto_atTop,
    hm'.comp hτ.tendsto_atTop,hL,hτ.tendsto_atTop.eventually HCL,?_,hmn,hmt,hbar,hmi,
    hs,hs',hcapO,e,d,he,hd',hri,hpe,hpD,hgap⟩
  intro j
  exact (ha j).1

end MaximumSelectionCompact
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.MaximumJensenFamily.selected_pole_compact_oai.{u_1} := @OAI.WeakMTWTransport.MaximumJensenFamily.selected_pole_compact_oai.{u_1}
