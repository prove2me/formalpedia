-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_uniform_cost_upper_taylor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:55.266777+00:00
-- url     : https://prove2.me/submissions/f1b89887-a555-4f41-be8e-3f91dfb45ad6

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
import Definitions.Def_OAIQ232A026
import Definitions.Def_OAIQ232A027

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ManifoldLipschitz
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma movingNormal_trivialization_exp {a x : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (p : TangentSpace 𝓘(ℝ,Model n) x) :
    movingNormal a (extChartAt 𝓘(ℝ,Model n) a x,
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p)
      = riemannianExp x p := by
  rw [movingNormal_eq ((extChartAt 𝓘(ℝ,Model n) a).map_source hx),
    (extChartAt 𝓘(ℝ,Model n) a).left_inv hx,
    Trivialization.symmL_continuousLinearMapAt]
  change x∈(chartAt (Model n) a).source
  simpa only [extChartAt_source] using hx

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

lemma tangent_chart_trivialization {a x : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) ⟨x,p⟩=
      (extChartAt 𝓘(ℝ,Model n) a x,
        (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p) := by
  rw [tangent_chart_apply,TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (by simpa only [extChartAt_source] using hx)]
  rfl

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

lemma trivialization_mem_minimizingChartParameters {a x : M} {K : Set M}
    (hKs : K⊆(extChartAt 𝓘(ℝ,Model n) a).source) (hx : x∈K)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x) :
    (extChartAt 𝓘(ℝ,Model n) a x,
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p)∈
      minimizingChartParameters (n := n) a K :=
  ⟨⟨x,p⟩,⟨hp,hx⟩,tangent_chart_trivialization (hKs hx) p⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CompactUniformSecondRemainder
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
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport

lemma compact_uniform_second_remainder {Q E : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set Q} (hP : IsCompact P) {F : Q → E → ℝ}
    (hF : ∀ q∈P, ContDiffAt ℝ ∞ (Function.uncurry F) (q,0)) :
    ∃ B>0, ∃ d>0, ∀ q∈P, ∀ z : E, ‖z‖<d →
      |F q z-F q 0-fderiv ℝ (F q) 0 z|≤B*‖z‖^2 := by
  let H := fun w : E×Q => fderiv ℝ (fderiv ℝ (F w.2)) w.1
  have hC : ∀ q∈P, ContinuousAt H (0,q) := by
    intro q hq
    exact (ContDiffAt.partial_snd_fderiv_two (hF q hq)).continuousAt.comp
      (x := (0,q)) (f := fun w : E×Q => (w.2,w.1))
      (continuousAt_snd.prodMk continuousAt_fst)
  obtain ⟨B,hB,HB⟩ := compact_eventually_fiberwise_bound hP
    (f := fun _ : Q => ()) continuous_const (g := fun _ : E => ())
    (continuousAt_const (x := (0:E))) (h := H) (fun q hq _ => hC q hq)
  have HS : ∀ᶠ z : E in 𝓝 0, ∀ q∈P, ()=() → ContDiffAt ℝ 2 (F q) z := by
    apply compact_eventually_fiberwise hP (f := fun _ : Q => ()) continuous_const
      (g := fun _ : E => ()) (continuousAt_const (x := (0:E)))
    intro q hq _
    have He := ((hF q hq).of_le
      (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hc : ContinuousAt (fun w : E×Q => (w.2,w.1)) (0,q) :=
      continuousAt_snd.prodMk continuousAt_fst
    filter_upwards [hc.tendsto.eventually He] with w hw
    exact hw.comp w.1 (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨d,hd,hnear⟩ := Metric.eventually_nhds_iff.mp (HB.and HS)
  refine ⟨B,hB,d,hd,?_⟩
  intro q hq z hz
  have Hrem := first_order_remainder_le_of_hessian_bound (convex_ball (0:E) d) hB.le
    (fun w hw => (hnear hw).2 q hq rfl) (fun w hw => (hnear hw).1 q hq rfl)
    (show (0:E)∈ball 0 d by simpa only [mem_ball,dist_self] using hd)
    (show z∈ball 0 d by simpa only [mem_ball,dist_zero_right] using hz)
  simpa only [sub_zero] using Hrem

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_RayAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology NNReal ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma minimizing_ray_tail_cost {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hp : z.2∈minimizingVectors z.1) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    cost (sprayFlow t z).1 (riemannianExp z.1 z.2)=(1-t)^2*‖z.2‖^2/2 := by
  have hm : dist z.1 (sprayFlow 1 z).1=1*‖z.2‖ := by
    simpa only [one_mul,riemannianExp_eq_sprayFlow] using (show dist z.1 (riemannianExp z.1 z.2)=‖z.2‖ from hp)
  have H := sprayFlow_minimizing_subinterval z ht ht1 hm
  rw [cost,riemannianExp_eq_sprayFlow]
  change dist (sprayFlow t z).1 (sprayFlow 1 z).1^2/2=_
  rw [H,mul_pow]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_UniformCostTaylor
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma half_cost_taylor_near_base (a : M) :
    ∃ C>0, ∃ d>0, ∃ K∈𝓝 a, ∀ x∈K, ∀ p v : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ‖v‖<d →
      |normalCost x ((1/2:ℝ) • p) v-normalCost x ((1/2:ℝ) • p) 0+
        inner ℝ ((1/2:ℝ) • p) v|≤C*‖v‖^2 := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨B,hB,hbound⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) a
  obtain ⟨K,hKn,hKs,hKc⟩ := local_compact_nhds
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a) hbound)
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let e := trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  let P := minimizingChartParameters (n := n) a K
  let F : (Model n×Model n) → Model n → ℝ :=
    fun q z => movingNormalCost a q.1 ((1/2:ℝ) • q.2) z
  have hF : ∀ q∈P, ContDiffAt ℝ ∞ (Function.uncurry F) (q,0) := by
    intro q hq
    have H := mem_minimizingChartParameters (fun x hx => (hKs hx).1) hq
    have hp := contracted_minimizer_mem_injectivityDomain H.2.2
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
    have hp' : e.symmL ℝ (χ.symm q.1) ((1/2:ℝ) • q.2)∈injectivityDomain (χ.symm q.1) :=
      by simpa only [map_smul] using hp
    exact (movingNormalCost_contDiffAt H.1 hp').comp (q,(0 : Model n))
      ((contDiffAt_fst.fst.prodMk ((contDiffAt_const (c := (1/2:ℝ))).smul contDiffAt_fst.snd)).prodMk contDiffAt_snd)
  obtain ⟨L,hL,d,hd,H⟩ := compact_uniform_second_remainder
    (isCompact_minimizingChartParameters hKc (fun x hx => (hKs hx).1)) hF
  refine ⟨L*B^2,by positivity,d/B,by positivity,K,hKn,?_⟩
  intro x hx p v hp hv
  let A := e.continuousLinearMapAt ℝ x
  have hpP : (χ x,A p)∈P :=
    trivialization_mem_minimizingChartParameters (fun x hx => (hKs hx).1) hx hp
  have hAv : ‖A v‖≤B*‖v‖ :=
    (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right (hKs hx).2.le (norm_nonneg _))
  have he : normalCost x ((1/2:ℝ) • p) = fun z => F (χ x,A p) (A z) := by
    funext z
    dsimp only [normalCost,F,movingNormalCost]
    rw [←map_smul,movingNormal_trivialization_exp (hKs hx).1,
      movingNormal_trivialization_exp (hKs hx).1]
  have hD : DifferentiableAt ℝ (F (χ x,A p)) 0 :=
    ((hF _ hpP).comp 0 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hder : fderiv ℝ (F (χ x,A p)) 0 (A v) = -inner ℝ ((1/2:ℝ) • p) v := by
    have hd0 : HasFDerivAt (F (χ x,A p)) (fderiv ℝ (F (χ x,A p)) 0) (A 0) := by
      simpa only [map_zero] using hD.hasFDerivAt
    have HD := hd0.comp 0 A.hasFDerivAt
    dsimp only [Function.comp_def] at HD
    rw [←he] at HD
    have HR := congrArg (fun L : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => L v) HD.fderiv.symm
    rw [normalCost_fderiv_zero (contracted_minimizer_mem_injectivityDomain hp
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1))] at HR
    exact HR
  have havd : ‖A v‖<d := hAv.trans_lt (by rw [mul_comm B]; exact (lt_div_iff₀ hB).mp hv)
  have HR := H _ hpP (A v) havd
  rw [hder] at HR
  have he0 := congrFun he 0
  have hev := congrFun he v
  simp only [map_zero] at he0
  rw [←he0,←hev,sub_neg_eq_add] at HR
  apply HR.trans
  calc
    L*‖A v‖^2≤L*(B*‖v‖)^2 := by gcongr
    _=(L*B^2)*‖v‖^2 := by ring

lemma exists_uniform_half_cost_taylor [Nonempty M] :
    ∃ C>0, ∃ d>0, ∀ x : M, ∀ p v : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ‖v‖<d →
      |normalCost x ((1/2:ℝ) • p) v-normalCost x ((1/2:ℝ) • p) 0+
        inner ℝ ((1/2:ℝ) • p) v|≤C*‖v‖^2 := by
  classical
  choose C hC d hd K hKn H using half_cost_taylor_near_base (n := n) (M := M)
  obtain ⟨s,hs⟩ := finite_cover_nhds hKn
  have hsn : s.Nonempty := by
    have hx : Classical.arbitrary M∈ ⋃ a∈s,K a := by rw [hs]; trivial
    obtain ⟨a,ha,_⟩ := mem_iUnion₂.mp hx
    exact ⟨a,ha⟩
  refine ⟨s.sup' hsn C,?_,s.inf' hsn d,?_,?_⟩
  · obtain ⟨a,ha⟩ := hsn
    exact (hC a).trans_le (Finset.le_sup' C ha)
  · exact (Finset.lt_inf'_iff hsn).mpr (fun a _ => hd a)
  · intro x p v hp hv
    have hx : x∈ ⋃ a∈s,K a := by rw [hs]; trivial
    obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp hx
    exact (H a x hxa p v hp (hv.trans_le (Finset.inf'_le d ha))).trans
      (mul_le_mul_of_nonneg_right (Finset.le_sup' C ha) (sq_nonneg _))

lemma exists_uniform_cost_upper_taylor_oai [Nonempty M] :
    ∃ C>0, ∃ d>0, ∀ x : M, ∀ p v : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ‖v‖<d →
      cost (riemannianExp x v) (riemannianExp x p)≤
        cost x (riemannianExp x p)-inner ℝ p v+C*‖v‖^2 := by
  obtain ⟨C,hC,d,hd,H⟩ := exists_uniform_half_cost_taylor (n := n) (M := M)
  refine ⟨2*C,by positivity,d,hd,?_⟩
  intro x p v hp hv
  have hrem := (abs_le.mp (H x p v hp hv)).2
  have hsplit := divided_cost_triangle (riemannianExp x v)
    (riemannianExp x ((1/2:ℝ) • p)) (riemannianExp x p)
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  have htail := minimizing_ray_tail_cost (z := ⟨x,p⟩) hp
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
  have hmid : cost x (riemannianExp x ((1/2:ℝ) • p))=‖p‖^2/8 := by
    rw [cost,show dist x (riemannianExp x ((1/2:ℝ) • p))=‖(1/2:ℝ) • p‖ from
      minimizingVectors_smul hp (by norm_num) (by norm_num),norm_smul]
    norm_num <;> ring
  have hfull : cost x (riemannianExp x p)=‖p‖^2/2 := by
    rw [cost,show dist x (riemannianExp x p)=‖p‖ from hp]
  have hflow : (sprayFlow (1/2) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1=
      riemannianExp x ((1/2:ℝ) • p) := (riemannianExp_smul x p (1/2)).symm
  rw [hflow] at htail
  norm_num at htail hsplit
  dsimp only [normalCost] at hrem
  rw [riemannianExp_zero,hmid,real_inner_smul_left] at hrem
  rw [htail] at hsplit
  rw [hfull]
  nlinarith only [hrem,hsplit]

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.exists_uniform_cost_upper_taylor_oai.{u_1} := @OAI.WeakMTWTransport.exists_uniform_cost_upper_taylor_oai.{u_1}
