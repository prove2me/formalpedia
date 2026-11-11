-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.exists_maximum_true_outer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:46:51.86554+00:00
-- url     : https://prove2.me/submissions/9643022a-d7d3-48a4-beb0-4398234ed313

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
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_original_outer_limit

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumActiveLimits
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
section MaximumActiveLimits
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

attribute [local instance] OAI.WeakMTWTransport.activeLimitDualGroup
attribute [local instance] OAI.WeakMTWTransport.activeLimitDualSpace
local instance activeLimitBilinearGroup_rbd06f1_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance activeLimitBilinearSpace_rbd06f1_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma MaximumDiagonal.active_weight_limits {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0))
    {r:Fin (Module.finrank ℝ (Model n)+1) → Model n}
    {m:Fin (Module.finrank ℝ (Model n)+1) → ℝ}
    (hr:Tendsto (fun k=>(J.first k).pj₀) atTop (𝓝 r))
    (hm:Tendsto (fun k=>(J.first k).w₀) atTop (𝓝 m)) :
    Tendsto (fun k=>(J.first k).pj (S.ν k)) atTop (𝓝 r) ∧
    Tendsto (fun k=>(J.first k).w (S.ν k)) atTop (𝓝 m) := by
  exact ⟨diagonal_tendsto_of_close hr hε (Eventually.of_forall (fun k=>(S.activeClose k).le)),
    diagonal_tendsto_of_close hm hε (Eventually.of_forall (fun k=>(S.weightClose k).le))⟩

lemma MaximumDiagonal.sample_pole_limit {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {L:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hL:Tendsto (fun k=>(J.first k).L) atTop (𝓝 L)) :
    Tendsto (fun k=>J.sampleL k (S.ν k)) atTop (𝓝 L) := by
  apply diagonal_tendsto_of_close hL hε
  exact Eventually.of_forall (fun k=>by simpa only [dist_eq_norm] using (S.LClose k).le)

end MaximumActiveLimits
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumTrueOuter
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
section MaximumTrueOuter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance maximumOuterFinite_rbd06f1_1 (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance maximumOuterComplete_rbd06f1_1 (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _
local instance maximumOuterDualGroup_rbd06f1_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumOuterDualSpace_rbd06f1_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumOuterBilinearGroup_rbd06f1_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumOuterBilinearSpace_rbd06f1_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma WeakMTW.exists_maximum_true_outer_oai
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃K>0,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
    uv∈densityDualClass (metricVolume n) lam cap x0 →
    ∀(α D bminus bplus:ℝ) (Bc Bo:ℝ → ℝ),∀ho:Continuous Bo,ContDiff ℝ ∞ Bo →
    (∀b∈Icc bminus bplus,StrictMono (fun s=>modifiedScalar α D Bo (b,s))) →
    ∀F:MaximumFamily (n:=n) uv.2 α D bminus bplus Bc Bo,
    ∀(a c:M) (N:Set (Model n)),
    ∀J:MaximumJensenFamily hmtw uv.2.continuous ho F a c N,
    ∀(ε:ℕ → ℝ),MaximumDiagonal J ε J.OuterSampleGood →
    Tendsto ε atTop (𝓝 0) → ∀(q:Model n) (β:ℝ),riemannianExp a q=c →
    Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto F.b atTop (𝓝 β) →
    ∀(r:Fin (Module.finrank ℝ (Model n)+1) → Model n)
      (m:Fin (Module.finrank ℝ (Model n)+1) → ℝ)
      (L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    Tendsto (fun k=>(J.first k).pj₀) atTop (𝓝 r) →
    Tendsto (fun k=>(J.first k).w₀) atTop (𝓝 m) →
    Tendsto (fun k=>(J.first k).L) atTop (𝓝 L) →
    ∀i,(show TangentSpace 𝓘(ℝ,Model n) a from r i)∈minimizingVectors a →
    0 < m i → ∀l κ:ℝ,
    deriv (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=l →
    iteratedDeriv 2 (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a (r i)))=κ →
    1 < l → κ < 0 →
    (∀d,d≠0 → 0 < m i*L d d-(κ/l^2)*
        (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) (r i) d)^2) →
    ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0 < V d d) ∧
      (∀d,m i*L d d-(κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) (r i) d)^2 ≤ V d d) ∧
      expJacobian (n:=n) (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
        (l⁻¹ • (reverseRay (⟨a,r i⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*(bilinearOperator V).det ≤
        (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*K*
          (expJacobian (n:=n) a (r i))^2 := by
  obtain ⟨K,hK,HK⟩:=hmtw.exists_original_outer_limit hlam hcap
  refine ⟨K,hK,?_⟩
  intro x0 uv huv α D bminus bplus Bc Bo ho hBo hmono F a c N J ε S hε q β he hQ hβ
    r m L hr hm hL i hmin hmi l κ hd hdd hl hκ hp
  obtain ⟨hb,_,_,_⟩:=S.limits J hε hQ he
  obtain ⟨hri,hwi⟩:=S.active_weight_limits hε hr hm
  have hLi:=S.sample_pole_limit hε hL
  apply HK x0 uv (modifiedScalar α D Bo) huv (modifiedScalar_contDiff hBo α D)
    a (fun k=>graphBaseCoordinate a (J.samplePoint k (S.ν k)).1)
    (fun k=>(J.first k).pj (S.ν k) i) F.b (fun k=>(J.first k).w (S.ν k) i)
    (fun k=>J.sampleL k (S.ν k)) β (m i) l κ (r i) L hmin hb
    (tendsto_pi_nhds.mp hri i) hβ (tendsto_pi_nhds.mp hwi i) hLi hd hdd hl hκ hp
  filter_upwards [(tendsto_pi_nhds.mp hwi i).eventually (lt_mem_nhds hmi)] with k hk
  have hS:=S.extra k
  have htarget:(graphBaseCoordinate a (J.samplePoint k (S.ν k)).1)∈
      (extChartAt 𝓘(ℝ,Model n) a).target:=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (S.poleSource k)
  exact ⟨htarget,hmono _ (Ioo_subset_Icc_self (F.parameter k)),hS.2.2.2.1 i,
    hS.2.2.1 i,hS.1,hS.2.1,hS.2.2.2.2 i hk⟩
end MaximumTrueOuter
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.exists_maximum_true_outer_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.exists_maximum_true_outer_oai.{u_1}
