-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_uniform_divided_hessian_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:56.509899+00:00
-- url     : https://prove2.me/submissions/d8e335b8-d3aa-4c3b-ba2c-8b6a87357202

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_CompactParameterJets
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

variable {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma compact_parameter_second_jet {K : Set Q} (hK : IsCompact K)
    {F : (ℝ×Q) → E → ℝ} {t : ℝ}
    (hF : ∀ q∈K, ContDiffAt ℝ ∞ (Function.uncurry F) ((t,q),0)) :
    ∃ B>0, ∀ᶠ s in 𝓝 t, ∀ q∈K,
      ContDiffAt ℝ 2 (F (s,q)) 0 ∧ ‖fderiv ℝ (fderiv ℝ (F (s,q))) 0‖≤B := by
  let H := fun z : ℝ×Q => fderiv ℝ (fderiv ℝ (F z)) 0
  have hH : ∀ q∈K, ContinuousAt H (t,q) := by
    intro q hq
    exact (ContDiffAt.partial_snd_fderiv_two (hF q hq)).continuousAt.comp
      (x := (t,q)) (f := fun z : ℝ×Q => (z,(0:E)))
      (continuousAt_id.prodMk continuousAt_const)
  obtain ⟨B,hB,HB⟩ := compact_eventually_fiberwise_bound hK
    (f := fun _ : Q => ()) continuous_const (g := fun _ : ℝ => ())
    (continuousAt_const (x := t)) (h := H) (fun q hq _ => hH q hq)
  have HS : ∀ᶠ s in 𝓝 t, ∀ q∈K, ()=() → ContDiffAt ℝ 2 (F (s,q)) 0 := by
    apply compact_eventually_fiberwise hK (f := fun _ : Q => ()) continuous_const
      (g := fun _ : ℝ => ()) (continuousAt_const (x := t))
    intro q hq _
    have He := ((hF q hq).of_le
      (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hc : ContinuousAt (fun z : ℝ×Q => (z,(0:E))) (t,q) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [hc.tendsto.eventually He] with z hz
    exact hz.comp (0:E) (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨B,hB,?_⟩
  filter_upwards [HB,HS] with s hb hs
  exact fun q hq => ⟨hs q hq rfl,hb q hq rfl⟩

end

open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma movingShortLegCost_contDiffAt {a : M} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingShortLegCost a)) ((1,(b,p)),0) := by
  let Z := (ℝ × (Model n × Model n)) × Model n
  have hA : ContMDiffAt 𝓘(ℝ,Z) 𝓘(ℝ,Model n) ∞
      (fun q : Z => movingNormal a (q.1.2.1,q.1.1 • (q.1.2.2+q.2))) ((1,(b,p)),0) := by
    refine (show ContMDiffAt 𝓘(ℝ,Model n × Model n) 𝓘(ℝ,Model n) ∞
      (movingNormal a) (b,(1:ℝ) • (p+0)) from by simpa using movingNormal_contMDiffAt hb).comp
      (f := fun q : Z => (q.1.2.1,q.1.1 • (q.1.2.2+q.2))) ((1,(b,p)),0) ?_
    exact (contDiffAt_fst.snd.fst.prodMk
      (contDiffAt_fst.fst.smul (contDiffAt_fst.snd.snd.add contDiffAt_snd))).contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,Z) 𝓘(ℝ,Model n) ∞
      (fun q : Z => movingNormal a q.1.2) ((1,(b,p)),0) :=
    (movingNormal_contMDiffAt (q := (b,p)) hb).comp ((1,(b,p)),0)
      contDiffAt_fst.snd.contMDiffAt
  have hC : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M × M => cost q.1 q.2)
      (movingNormal a (b,(1:ℝ) • (p+0)),movingNormal a (b,p)) := by
    simpa only [add_zero,one_smul,riemannianExp_zero] using
      cost_contMDiffAt_of_injectivityDomain
        (⟨movingNormal a (b,p),0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
        (zero_mem_injectivityDomain (movingNormal a (b,p)))
  exact (hC.comp ((1,(b,p)),0) (hA.prodMk hB)).contDiffAt

lemma shortLeg_second_bound_near_base (R : ℝ) (a : M) :
    ∃ C : ℝ≥0, ∃ K∈𝓝 a, ∀ᶠ t in 𝓝 (1:ℝ), ∀ x∈K,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) x, ‖p‖≤R →
      ContDiffAt ℝ 2 (shortLegCost x t p) 0 ∧
      ∀ k : TangentSpace 𝓘(ℝ,Model n) x,
      ‖fderiv ℝ (fderiv ℝ (shortLegCost x t p)) 0 k k‖≤C*‖k‖^2 := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨B,hBpos,hB⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) a
  obtain ⟨K,hKn,hKs,hKc⟩ := local_compact_nhds
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a) hB)
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let P := (χ '' K) ×ˢ closedBall (0 : Model n) (B*R)
  have hPc : IsCompact P :=
    (hKc.image_of_continuousOn ((continuousOn_extChartAt a).mono
      (fun x hx => (hKs hx).1))).prod (isCompact_closedBall _ _)
  obtain ⟨D,hDpos,HD⟩ := compact_parameter_second_jet hPc
    (F := movingShortLegCost a) (t := 1) (fun q hq => movingShortLegCost_contDiffAt (by
      obtain ⟨x,hx,hxq⟩ := hq.1
      rw [←hxq]
      exact χ.map_source (hKs hx).1))
  refine ⟨⟨D*B^2,mul_nonneg hDpos.le (sq_nonneg B)⟩,K,hKn,?_⟩
  filter_upwards [HD] with t ht
  intro x hx p hp
  let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x
  have hpP : (χ x,A p)∈P := by
    refine ⟨mem_image_of_mem χ hx,?_⟩
    rw [mem_closedBall,dist_zero_right]
    exact (A.le_opNorm p).trans (mul_le_mul (hKs hx).2.le hp (norm_nonneg _) hBpos.le)
  have he : shortLegCost x t p = (fun h => movingShortLegCost a (t,(χ x,A p)) (A h)) := by
    funext h
    dsimp only [shortLegCost,movingShortLegCost]
    rw [←map_add,←map_smul,movingNormal_trivialization_exp (hKs hx).1,
      movingNormal_trivialization_exp (hKs hx).1]
  rw [he]
  have HD' := ht (χ x,A p) hpP
  refine ⟨(show ContDiffAt ℝ 2 (movingShortLegCost a (t,(χ x,A p))) (A 0) from by
    simpa only [map_zero] using HD'.1).comp 0 A.contDiff.contDiffAt,?_⟩
  intro k
  rw [second_fderiv_comp_linear_zero HD'.1 A k]
  let H := fderiv ℝ (fderiv ℝ (movingShortLegCost a (t,(χ x,A p)))) 0
  have hAk : ‖A k‖≤B*‖k‖ :=
    (A.le_opNorm k).trans (mul_le_mul_of_nonneg_right (hKs hx).2.le (norm_nonneg _))
  calc
    ‖H (A k) (A k)‖≤‖H (A k)‖*‖A k‖ := (H (A k)).le_opNorm _
    _≤(‖H‖*‖A k‖)*‖A k‖ := mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _)
    _≤(D*‖A k‖)*‖A k‖ := by gcongr; exact HD'.2
    _≤(D*(B*‖k‖))*(B*‖k‖) := by gcongr
    _=(D*B^2)*‖k‖^2 := by ring

lemma exists_uniform_shortLeg_second_bound (R : ℝ) :
    ∃ C : ℝ≥0, ∀ᶠ t in 𝓝 (1:ℝ), ∀ x : M,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) x, ‖p‖≤R →
      ContDiffAt ℝ 2 (shortLegCost x t p) 0 ∧
      ∀ k : TangentSpace 𝓘(ℝ,Model n) x,
      ‖fderiv ℝ (fderiv ℝ (shortLegCost x t p)) 0 k k‖≤C*‖k‖^2 := by
  classical
  choose C K hKn hK using shortLeg_second_bound_near_base (n := n) (M := M) R
  obtain ⟨s,hs⟩ := finite_cover_nhds hKn
  refine ⟨s.sup C,?_⟩
  have HT := (eventually_all_finset s).mpr (fun a _ => hK a)
  filter_upwards [HT] with t ht
  intro x p hp
  have hx : x∈ ⋃ a∈s,K a := by rw [hs]; trivial
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp hx
  have H := ht a ha x hxa p hp
  refine ⟨H.1,fun k => (H.2 k).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.le_sup (f := C) ha) (sq_nonneg _)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_JetPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

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
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_QuantitativeDividedAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

lemma splitTrialValue_middle_shortLeg {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p∈injectivityDomain x)
    (hF : ContDiffAt ℝ 2 (shortLegCost x t p) 0) :
    splitTrialValue x t 0 k p = t*‖k‖^2+
      fderiv ℝ (fderiv ℝ (shortLegCost x t p)) 0 k k/(1-t) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hline : Tendsto (fun r : ℝ => p+r • k) (𝓝 0) (𝓝 p) := by
    simpa only [ContinuousAt,zero_smul,add_zero] using
      (show ContinuousAt (fun r : ℝ => p+r • k) 0 from by fun_prop)
  have he : (fun r : ℝ => splitNormalAction x t p (r • (0:V),p+r • k)) =ᶠ[𝓝 0]
      (fun r : ℝ => t*(‖p+r • k‖^2/2)+shortLegCost x t p (r • k)/(1-t)) := by
    filter_upwards [hline.eventually (prefixAction_axis_near hp)] with r hr
    simp only [splitNormalAction,smul_zero,riemannianExp_zero,shortLegCost]
    have H : cost x (riemannianExp x (t • (p+r • k)))/t=t*(‖p+r • k‖^2/2) := by
      simpa only [prefixAction,riemannianExp_zero] using hr
    rw [H]
  have hnorm : ContDiffAt ℝ 2 (fun v : V => ‖v‖^2/2) p :=
    ((half_norm_sq_contDiff (E := V)).of_le
      (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have hnline : ContDiffAt ℝ 2 (fun r : ℝ => ‖p+r • k‖^2/2) 0 := by
    exact (show ContDiffAt ℝ 2 (fun v : V => ‖v‖^2/2) (p+(0:ℝ) • k) from by
      simpa only [zero_smul,add_zero] using hnorm).comp (f := fun r:ℝ => p+r • k) 0 (by fun_prop)
  have hsline : ContDiffAt ℝ 2 (fun r : ℝ => shortLegCost x t p (r • k)) 0 := by
    exact (show ContDiffAt ℝ 2 (shortLegCost x t p) ((0:ℝ) • k) from by
      simpa only [zero_smul] using hF).comp (f := fun r:ℝ => r • k) 0 (by fun_prop)
  rw [splitTrialValue,he.iteratedDeriv_eq 2,
    iteratedDeriv_fun_add (contDiffAt_const.mul hnline) (hsline.div_const (1-t)),
    iteratedDeriv_const_mul t hnline]
  have hN := iteratedDeriv_two_affine_line hnorm k
  rw [half_norm_sq_second_fderiv,real_inner_self_eq_norm_sq] at hN
  have hS := iteratedDeriv_two_affine_line hF k
  simp only [zero_add] at hS
  rw [hN,iteratedDeriv_div_const,hS]

lemma exists_uniform_scaled_middle_bound (R : ℝ) :
    ∃ C>0, ∀ᶠ t in 𝓝 (1:ℝ), ∀ x : M,
      ∀ p k : TangentSpace 𝓘(ℝ,Model n) x, ‖p‖≤R → 0<t → t<1 →
      t • p∈injectivityDomain x → (1-t)*splitTrialValue x t 0 k p ≤ C*‖k‖^2 := by
  obtain ⟨B,HB⟩ := exists_uniform_shortLeg_second_bound (n := n) (M := M) R
  refine ⟨(B:ℝ)+1,by positivity,?_⟩
  filter_upwards [HB] with t ht
  intro x p k hp h0 h1 hpre
  have H := ht x p hp
  rw [splitTrialValue_middle_shortLeg hpre H.1]
  have he : (1-t)*(t*‖k‖^2+
      fderiv ℝ (fderiv ℝ (shortLegCost x t p)) 0 k k/(1-t)) =
      (1-t)*t*‖k‖^2+fderiv ℝ (fderiv ℝ (shortLegCost x t p)) 0 k k := by
    field_simp [sub_ne_zero.mpr h1.ne']
  rw [he]
  have hB := (le_abs_self (fderiv ℝ (fderiv ℝ (shortLegCost x t p)) 0 k k)).trans
    (by simpa only [Real.norm_eq_abs] using H.2 k)
  have hcoef : (1-t)*t≤1 := by nlinarith
  have Hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖k‖)
  nlinarith

lemma exists_uniform_divided_hessian_gap_oai (R : ℝ) :
    ∃ c>0, ∀ᶠ t in 𝓝 (1:ℝ), ∀ x : M,
      ∀ p xi : TangentSpace 𝓘(ℝ,Model n) x, ‖p‖≤R → 0<t → t<1 →
      p∈injectivityDomain x →
      hessianValue x p xi+c*(1-t)*‖xi‖^2 ≤ hessianValue x (t • p) xi/t := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_scaled_middle_bound (n := n) (M := M) R
  refine ⟨C⁻¹,inv_pos.mpr hC,?_⟩
  filter_upwards [HC] with t ht
  intro x p xi hp h0 h1 hpre
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hpre) h0 h1
  by_cases hxi : xi=0
  · subst xi
    simp only [hessianValue_eq_normalHessian hpre,hessianValue_eq_normalHessian hleft,
      map_zero,norm_zero,zero_pow two_ne_zero,mul_zero,add_zero,zero_div,le_refl]
  have hpair : inner ℝ xi xi≠0 := inner_self_ne_zero.mpr hxi
  have hright := shifted_injectivityDomain_of_injectivityDomain hpre h0.le h1
  obtain ⟨hpos,hSchur⟩ := splitTrialValue_schur h0 h1 hpre hleft hright hpair
  rw [splitTrialValue_source,real_inner_self_eq_norm_sq] at hSchur
  have HB := ht x p xi hp h0 h1 hleft
  have Hlower : C⁻¹*(1-t)*‖xi‖^2≤(‖xi‖^2)^2/splitTrialValue x t 0 xi p := by
    apply (le_div_iff₀ hpos).mpr
    have Hmul := mul_le_mul_of_nonneg_right HB (sq_nonneg ‖xi‖)
    have Hdiv := mul_le_mul_of_nonneg_left Hmul (inv_nonneg.mpr hC.le)
    convert! Hdiv using 1 <;> field_simp [hC.ne']
  linarith

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.exists_uniform_divided_hessian_gap_oai.{u_1} := @OAI.WeakMTWTransport.exists_uniform_divided_hessian_gap_oai.{u_1}
