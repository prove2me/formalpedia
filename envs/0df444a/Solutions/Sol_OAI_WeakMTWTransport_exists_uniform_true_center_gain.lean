-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_uniform_true_center_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:59.297196+00:00
-- url     : https://prove2.me/submissions/425a3002-f888-4a2f-87e1-f8a8689cc9f2

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
import Theorems.Thm_OAI_WeakMTWTransport_exists_reverse_exp_divided_isotropic_gain
import Theorems.Thm_OAI_WeakMTWTransport_fixedJoinMiddle_uniform_interval_crossing

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

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_MixedContinuity
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
lemma compact_parameter_second_jet_on_graph {Q E : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set Q} (hK : IsCompact K) {v : Q → E} (hv : Continuous v)
    {F : (ℝ×Q) → E → ℝ} {t : ℝ}
    (hF : ∀ q∈K, ContDiffAt ℝ ∞ (Function.uncurry F) ((t,q),v q)) :
    ∃ B>0, ∀ᶠ s in 𝓝 t, ∀ q∈K,
      ContDiffAt ℝ 2 (F (s,q)) (v q) ∧
      ‖fderiv ℝ (fderiv ℝ (F (s,q))) (v q)‖≤B := by
  let H := fun z : ℝ×Q => fderiv ℝ (fderiv ℝ (F z)) (v z.2)
  have hc : Continuous (fun z : ℝ×Q => (z,v z.2)) := continuous_id.prodMk (hv.comp continuous_snd)
  have hH : ∀ q∈K, ContinuousAt H (t,q) := by
    intro q hq
    exact (ContDiffAt.partial_snd_fderiv_two (hF q hq)).continuousAt.comp
      (x := (t,q)) (f := fun z : ℝ×Q => (z,v z.2)) hc.continuousAt
  obtain ⟨B,hB,HB⟩ := compact_eventually_fiberwise_bound hK
    (f := fun _ : Q => ()) continuous_const (g := fun _ : ℝ => ())
    (continuousAt_const (x := t)) (h := H) (fun q hq _ => hH q hq)
  have HS : ∀ᶠ s in 𝓝 t, ∀ q∈K, ()=() → ContDiffAt ℝ 2 (F (s,q)) (v q) := by
    apply compact_eventually_fiberwise hK (f := fun _ : Q => ()) continuous_const
      (g := fun _ : ℝ => ()) (continuousAt_const (x := t))
    intro q hq _
    have He := ((hF q hq).of_le
      (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    filter_upwards [(hc.continuousAt (x := (t,q))).tendsto.eventually He] with z hz
    exact hz.comp (v z.2) (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨B,hB,?_⟩
  filter_upwards [HB,HS] with s hb hs
  exact fun q hq => ⟨hs q hq rfl,hb q hq rfl⟩
end WeakMTWTransport

end

end OAI
end

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_MovingNormalEndpointJoin
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

lemma movingNormalEndpointJoinAction_contDiffAt {a c : M} {b e p : Model n} {h : ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (he : e∈(extChartAt 𝓘(ℝ,Model n) c).target)
    (h0 : h≠0) (h1 : h≠1)
    (hend : (extChartAt 𝓘(ℝ,Model n) c).symm e=movingNormal a (b,p))
    (hleft : h • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hright : (1-h) • (sprayFlow h
      (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
        (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h
        (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
          (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
            ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingNormalEndpointJoinAction a c)) ((h,(b,e)),(0,p)) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  let Q := (ℝ×(Model n×Model n))×(Model n×Model n)
  let q : Q := ((h,(b,e)),(0,p))
  have hA : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun z : Q => movingNormal a (z.1.2.1,0)) q :=
    (movingNormal_contMDiffAt (q := (b,0)) hb).comp q
      (contDiffAt_fst.snd.fst.prodMk contDiffAt_const).contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun z : Q => movingNormal a (z.1.2.1,z.1.1 • z.2.2)) q :=
    (movingNormal_contMDiffAt (q := (b,h • p)) hb).comp q
      (contDiffAt_fst.snd.fst.prodMk (contDiffAt_fst.fst.smul contDiffAt_snd.snd)).contMDiffAt
  have hC : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun z : Q => movingNormal c (z.1.2.2,z.2.1)) q :=
    (movingNormal_contMDiffAt (q := (e,0)) he).comp q
      (contDiffAt_fst.snd.snd.prodMk contDiffAt_snd.fst).contMDiffAt
  have hc₁ := cost_contMDiffAt_of_injectivityDomain
    (⟨x,h • L p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hleft
  have hc₂ := cost_contMDiffAt_of_injectivityDomain
    (⟨(sprayFlow h (⟨x,L p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      (1-h) • (sprayFlow h (⟨x,L p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hright
  have hc₁' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => cost z.1 z.2)
      (movingNormal a (b,0),movingNormal a (b,h • p)) := by
    simpa only [movingNormal_eq hb,map_zero,riemannianExp_zero,map_smul] using hc₁
  have hc₂' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => cost z.1 z.2)
      (movingNormal a (b,h • p),movingNormal c (e,0)) := by
    dsimp only at hc₂
    rw [shifted_exp_endpoint] at hc₂
    simp only [movingNormal_eq he,map_zero,riemannianExp_zero,hend]
    simpa only [movingNormal_eq hb,map_smul,riemannianExp_smul] using hc₂
  exact ((hc₁'.comp q (hA.prodMk hB)).contDiffAt.div contDiffAt_fst.fst h0).add
    ((hc₂'.comp q (hB.prodMk hC)).contDiffAt.div
      (contDiffAt_const.sub contDiffAt_fst.fst) (sub_ne_zero.mpr h1.symm))

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma movingNormalEndpointJoinAction_trivialization {a c x y : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hy : y∈(extChartAt 𝓘(ℝ,Model n) c).source) (h : ℝ)
    (u : TangentSpace 𝓘(ℝ,Model n) y) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    movingNormalEndpointJoinAction a c
      (h,((extChartAt 𝓘(ℝ,Model n) a) x,(extChartAt 𝓘(ℝ,Model n) c) y))
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) c).continuousLinearMapAt ℝ y u,
       (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x v)=
      normalEndpointJoinAction x y h (u,v) := by
  dsimp only [movingNormalEndpointJoinAction,normalEndpointJoinAction]
  rw [← map_zero ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x),
    ←map_smul,movingNormal_trivialization_exp hx,movingNormal_trivialization_exp hx,
    movingNormal_trivialization_exp hy,riemannianExp_zero]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_UniformRegularSplit
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

lemma uniformly_shifted_injectivityDomain_near_one (R : ℝ) :
    ∀ᶠ h in 𝓝 (1:ℝ), ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      ‖p‖ ≤ R → (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  let Z : ℝ × TangentBundle 𝓘(ℝ,Model n) M → TangentBundle 𝓘(ℝ,Model n) M :=
    fun q => tangentScale (1-q.1) (sprayFlow q.1 q.2)
  have hZ : ContMDiff (𝓘(ℝ,ℝ).prod (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)))
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ Z :=
    contMDiff_tangentScale.comp ((contMDiff_const.sub contMDiff_fst).prodMk contMDiff_sprayFlow)
  have H := compact_eventually_fiberwise
    (isCompact_bundle_disk (B := M) (F := Model n)
      (E := fun x => TangentSpace 𝓘(ℝ,Model n) x) R)
    (f := fun _ => ()) continuous_const (g := fun _ : ℝ => ())
    (continuousAt_const (x := 1)) (P := fun h p => (Z (h,p)).2∈injectivityDomain (Z (h,p)).1)
    (by
      intro p _ _
      change ∀ᶠ q in 𝓝 (1,p), Z q ∈ {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈injectivityDomain z.1}
      apply hZ.continuous.continuousAt.eventually
      apply isOpen_total_injectivityDomain.mem_nhds
      change (1-(1:ℝ)) • (sprayFlow 1 p).2∈injectivityDomain (sprayFlow 1 p).1
      rw [sub_self,zero_smul]
      exact zero_mem_injectivityDomain _)
  exact H.mono fun _ hshift base velocity hbound =>
    hshift ⟨base,velocity⟩ hbound rfl

lemma exists_uniform_regular_split (R : ℝ) :
    ∃ h : ℝ, 0 < h ∧ h < 1 ∧ ∀ x : M,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) x, ‖p‖ ≤ R → p∈minimizingVectors x →
      h • p∈injectivityDomain x ∧
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  have H : ∀ᶠ h in 𝓝[<] (1:ℝ), 0 < h ∧ h < 1 ∧ ∀ x : M,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) x, ‖p‖ ≤ R →
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
    filter_upwards [(uniformly_shifted_injectivityDomain_near_one (n := n) (M := M) R).filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with h hh h0 h1
    exact ⟨h0,h1,hh⟩
  obtain ⟨h,h0,h1,hh⟩ := H.exists
  exact ⟨h,h0,h1,fun x p hp hm =>
    ⟨contracted_minimizer_mem_injectivityDomain hm h0 h1,hh x p hp⟩⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MixedOperator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

omit [CompleteSpace F] in
lemma mixedOperator_norm_le (B : F →L[ℝ] E →L[ℝ] ℝ) {a : ℝ}
    (ha : 0≤a) (hB : ∀ v w, |B v w|≤a*‖v‖*‖w‖) :
    ‖mixedOperator B‖≤a := by
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro v
  have he : ‖mixedOperator B v‖=‖B v‖ :=
    (InnerProductSpace.toDual ℝ E).symm.norm_map (B v)
  rw [he]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg ha (norm_nonneg v))
  intro w
  simpa only [Real.norm_eq_abs] using hB v w

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_UniformFixedCrossing
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

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
  (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma minimizing_norm_le_diam {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) : ‖p‖ ≤ Metric.diam (univ : Set M) := by
  rw [←hp]
  exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)

lemma exists_actual_uniform_regular_split :
    ∃ h : ℝ, 0 < h ∧ h < 1 ∧ ∀ x : M,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
        h • p∈injectivityDomain x ∧
        (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
          injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  obtain ⟨h,hh,hh1,Hh⟩ := exists_uniform_regular_split (n := n) (M := M) (Metric.diam (univ : Set M))
  exact ⟨h,hh,hh1,fun x p hp => Hh x p (minimizing_norm_le_diam hp) hp⟩

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

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_NormalEndpointLog
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

lemma isCompact_minimizingRays_between {K L : Set M}
    (hK : IsCompact K) (hL : IsCompact L) :
    IsCompact {z : TangentBundle 𝓘(ℝ,Model n) M |
      z.2∈minimizingVectors z.1 ∧ z.1∈K ∧ riemannianExp z.1 z.2∈L} := by
  exact (isCompact_total_minimizingVectors (n := n) (M := M)).inter_right
    ((hK.isClosed.preimage (FiberBundle.continuous_proj _ _)).inter
      (hL.isClosed.preimage contMDiff_riemannianExp.continuous))

lemma continuousOn_riemannianExp_chart (c : M) :
    ContinuousOn (fun z : TangentBundle 𝓘(ℝ,Model n) M =>
      (extChartAt 𝓘(ℝ,Model n) c) (riemannianExp z.1 z.2))
      {z | riemannianExp z.1 z.2∈(extChartAt 𝓘(ℝ,Model n) c).source} :=
  (continuousOn_extChartAt c).comp contMDiff_riemannianExp.continuous.continuousOn
    (fun _ hz => hz)

lemma continuousOn_endpointChartParameters {a c : M} {K L : Set M}
    (hKs : K⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hLs : L⊆(extChartAt 𝓘(ℝ,Model n) c).source) :
    ContinuousOn (fun z : TangentBundle 𝓘(ℝ,Model n) M =>
      ((extChartAt 𝓘(ℝ,Model n) a) z.1,
        ((extChartAt 𝓘(ℝ,Model n) c) (riemannianExp z.1 z.2),
         (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
            (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) z).2)))
      {z : TangentBundle 𝓘(ℝ,Model n) M |
        z.2∈minimizingVectors z.1 ∧ z.1∈K ∧ riemannianExp z.1 z.2∈L} := by
  let S := {z : TangentBundle 𝓘(ℝ,Model n) M |
    z.2∈minimizingVectors z.1 ∧ z.1∈K ∧ riemannianExp z.1 z.2∈L}
  have hX : ContinuousOn (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)) S :=
    (continuousOn_extChartAt _).mono
      (fun z hz => (tangent_chart_source_iff _ z).mpr (hKs hz.2.1))
  have hY : ContinuousOn (fun z : TangentBundle 𝓘(ℝ,Model n) M =>
      (extChartAt 𝓘(ℝ,Model n) c) (riemannianExp z.1 z.2)) S :=
    (continuousOn_riemannianExp_chart c).mono (fun z hz => hLs hz.2.2)
  have H := hX.fst.prodMk (hY.prodMk hX.snd)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  rw [tangent_chart_apply]

lemma isCompact_minimizingEndpointChartParameters {a c : M} {K L : Set M}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKs : K⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hLs : L⊆(extChartAt 𝓘(ℝ,Model n) c).source) :
    IsCompact (minimizingEndpointChartParameters (n := n) a c K L) :=
  (isCompact_minimizingRays_between hK hL).image_of_continuousOn
    (continuousOn_endpointChartParameters hKs hLs)

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] in
lemma tangent_symmL_trivialization {a x : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (p : TangentSpace 𝓘(ℝ,Model n) x) :
    (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p)=p :=
  Trivialization.symmL_continuousLinearMapAt _
    (by simpa only [TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx) p

lemma trivialization_mem_minimizingEndpointChartParameters {a c x : M} {K L : Set M}
    (hx : x∈K) (hxa : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    (hy : riemannianExp x p∈L) :
    ((extChartAt 𝓘(ℝ,Model n) a) x,
      ((extChartAt 𝓘(ℝ,Model n) c) (riemannianExp x p),
       (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p))∈
        minimizingEndpointChartParameters a c K L := by
  refine ⟨⟨x,p⟩,⟨hp,hx,hy⟩,?_⟩
  simp only [tangent_chart_trivialization hxa]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MixedTrivializationBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

local instance tangentFiniteTrivBound_rdf1735_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
attribute [local instance] OAI.WeakMTWTransport.endpointProductNormedGroupTriv
attribute [local instance] OAI.WeakMTWTransport.endpointProductNormedSpaceTriv
local instance endpointDualNormedGroupTriv_rdf1735_1 (x y : M) :
    NormedAddCommGroup ((TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ) :=
  inferInstance
local instance endpointDualNormedSpaceTriv_rdf1735_1 (x y : M) :
    NormedSpace ℝ ((TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ) :=
  inferInstance
lemma normalEndpointMixedOperator_norm_trivialization_le {a c x y : M} {h B D : ℝ}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hy : y∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hB : 0≤B) (hD : 0≤D)
    (hAx : ‖(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x‖≤B)
    (hAy : ‖(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) c).continuousLinearMapAt ℝ y‖≤D)
    (p : TangentSpace 𝓘(ℝ,Model n) x)
    (hF : ContDiffAt ℝ 2
      (movingNormalEndpointJoinAction a c
        (h,((extChartAt 𝓘(ℝ,Model n) a) x,(extChartAt 𝓘(ℝ,Model n) c) y)))
      (0,(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p)) :
    ‖normalEndpointMixedOperator x y h p‖≤
      ‖fderiv ℝ (fderiv ℝ (movingNormalEndpointJoinAction a c
        (h,((extChartAt 𝓘(ℝ,Model n) a) x,(extChartAt 𝓘(ℝ,Model n) c) y))))
        (0,(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p)‖*D*B := by
  let Ax := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x
  let Ay := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) c).continuousLinearMapAt ℝ y
  let L := Ay.prodMap Ax
  let F := movingNormalEndpointJoinAction a c
    (h,((extChartAt 𝓘(ℝ,Model n) a) x,(extChartAt 𝓘(ℝ,Model n) c) y))
  let J := fderiv ℝ (fderiv ℝ F) (0,Ax p)
  have he : normalEndpointJoinAction x y h=fun z => F (L z) := by
    funext z
    exact (movingNormalEndpointJoinAction_trivialization hx hy h z.1 z.2).symm
  change ‖mixedOperator _‖≤‖J‖*D*B
  apply mixedOperator_norm_le _ (by positivity)
  intro v w
  rw [negativeMixedForm_apply,abs_neg,he]
  have H := second_fderiv_comp_affine (f := F) L 0 (0,p)
    (by simpa only [zero_add,L,ContinuousLinearMap.coe_prodMap',Prod.map_apply,map_zero] using hF) (v,0) (0,w)
  have H' : fderiv ℝ (fderiv ℝ (fun z => F (L z))) (0,p) (v,0) (0,w)=
      J (Ay v,0) (0,Ax w) := by
    simpa only [zero_add,L,ContinuousLinearMap.coe_prodMap',Prod.map_apply,map_zero,J] using H
  rw [H',←Real.norm_eq_abs]
  have hv : ‖Ay v‖≤D*‖v‖ := (Ay.le_opNorm v).trans (mul_le_mul_of_nonneg_right hAy (norm_nonneg _))
  have hw : ‖Ax w‖≤B*‖w‖ := (Ax.le_opNorm w).trans (mul_le_mul_of_nonneg_right hAx (norm_nonneg _))
  calc
    ‖J (Ay v,0) (0,Ax w)‖≤‖J (Ay v,0)‖*‖((0:Model n),Ax w)‖ := (J _).le_opNorm _
    _≤(‖J‖*‖(Ay v,(0:Model n))‖)*‖((0:Model n),Ax w)‖ := by gcongr; exact J.le_opNorm _
    _=(‖J‖*‖Ay v‖)*‖Ax w‖ := by simp
    _≤(‖J‖*(D*‖v‖))*(B*‖w‖) := by gcongr
    _=(‖J‖*D*B)*‖v‖*‖w‖ := by ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_UniformMixedBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

lemma movingNormalEndpointJoinAction_chart_contDiffAt {a c x : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hy : riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hh : 0<h) (hh1 : h<1)
    (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingNormalEndpointJoinAction a c))
      ((h,((extChartAt 𝓘(ℝ,Model n) a) x,
        (extChartAt 𝓘(ℝ,Model n) c) (riemannianExp x p))),
       (0,(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p)) := by
  apply movingNormalEndpointJoinAction_contDiffAt
    ((extChartAt 𝓘(ℝ,Model n) a).map_source hx)
    ((extChartAt 𝓘(ℝ,Model n) c).map_source hy) hh.ne' hh1.ne
  · rw [(extChartAt 𝓘(ℝ,Model n) c).left_inv hy,movingNormal_trivialization_exp hx]
  · rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv hx,tangent_symmL_trivialization hx]
    exact hleft
  · rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv hx,tangent_symmL_trivialization hx]
    exact hright

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma movingEndpointFamily_contDiffAt {a c : M} {h : ℝ}
    {q : Model n×(Model n×Model n)}
    (H : ContDiffAt ℝ ∞ (Function.uncurry (movingNormalEndpointJoinAction a c))
      ((h,(q.1,q.2.1)),(0,q.2.2))) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingEndpointFamily a c)) ((h,q),(0,q.2.2)) := by
  exact H.comp ((h,q),(0,q.2.2))
    ((contDiffAt_fst.fst.prodMk
      (contDiffAt_fst.snd.fst.prodMk contDiffAt_fst.snd.snd.fst)).prodMk contDiffAt_snd)

lemma compact_movingEndpointFamily_bound {a c : M} {h : ℝ} {K L : Set M}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKs : K⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hLs : L⊆(extChartAt 𝓘(ℝ,Model n) c).source)
    (hh : 0<h) (hh1 : h<1)
    (Hsplit : ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      h • p∈injectivityDomain x ∧
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∃ B>0, ∀ᶠ s in 𝓝 h, ∀ q∈minimizingEndpointChartParameters (n := n) a c K L,
      ContDiffAt ℝ 2 (movingEndpointFamily a c (s,q)) (0,q.2.2) ∧
      ‖fderiv ℝ (fderiv ℝ (movingEndpointFamily a c (s,q))) (0,q.2.2)‖≤B := by
  apply compact_parameter_second_jet_on_graph
    (isCompact_minimizingEndpointChartParameters hK hL hKs hLs)
    (v := fun q : Model n×(Model n×Model n) => (0,q.2.2))
    (continuous_const.prodMk continuous_snd.snd)
  intro q hq
  obtain ⟨z,hz,rfl⟩ := hq
  have hx := hKs hz.2.1
  have hy := hLs hz.2.2
  apply movingEndpointFamily_contDiffAt
  simp only [tangent_chart_trivialization hx]
  exact movingNormalEndpointJoinAction_chart_contDiffAt hx hy hh hh1
    (Hsplit z.1 z.2 hz.1).1 (Hsplit z.1 z.2 hz.1).2

lemma normalEndpointMixedOperator_bound_near_pair {h : ℝ} (hh : 0<h) (hh1 : h<1)
    (Hsplit : ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      h • p∈injectivityDomain x ∧
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (a c : M) :
    ∃ C>0, ∃ U∈𝓝 (a,c), ∀ᶠ s in 𝓝 h,
      ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
        (x,riemannianExp x p)∈U → p∈minimizingVectors x →
          ‖normalEndpointMixedOperator x (riemannianExp x p) s p‖≤C := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨B,hBpos,hB⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) a
  obtain ⟨D,hDpos,hD⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c
  obtain ⟨K,hKn,hKs,hKc⟩ := local_compact_nhds
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a) hB)
  obtain ⟨L,hLn,hLs,hLc⟩ := local_compact_nhds
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) c) hD)
  obtain ⟨E,hE,HE⟩ := compact_movingEndpointFamily_bound hKc hLc
    (fun x hx => (hKs hx).1) (fun y hy => (hLs hy).1) hh hh1 Hsplit
  refine ⟨E*D*B,mul_pos (mul_pos hE hDpos) hBpos,K×ˢL,prod_mem_nhds hKn hLn,?_⟩
  filter_upwards [HE] with s hs
  intro x p hxy hp
  have H := hs _ (trivialization_mem_minimizingEndpointChartParameters hxy.1
    (hKs hxy.1).1 hp hxy.2)
  exact (normalEndpointMixedOperator_norm_trivialization_le
    (hKs hxy.1).1 (hLs hxy.2).1 hBpos.le hDpos.le
    (hKs hxy.1).2.le (hLs hxy.2).2.le p H.1).trans (by
      change ‖fderiv ℝ (fderiv ℝ (movingEndpointFamily a c (s,_))) _‖*D*B≤E*D*B
      gcongr
      exact H.2)

lemma normalEndpointMixedOperator_uniform_bound {h : ℝ} (hh : 0<h) (hh1 : h<1)
    (Hsplit : ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      h • p∈injectivityDomain x ∧
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∃ C>0, ∀ᶠ s in 𝓝 h, ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ‖normalEndpointMixedOperator x (riemannianExp x p) s p‖≤C := by
  classical
  have H := fun z : M×M => normalEndpointMixedOperator_bound_near_pair hh hh1 Hsplit z.1 z.2
  choose C hC U hU HU using H
  obtain ⟨S,hS⟩ := finite_cover_nhds hU
  let B := 1+∑ z∈S, |C z|
  have hB : 0<B := by dsimp [B] <;> positivity
  refine ⟨B,hB,?_⟩
  have HT := (eventually_all_finset S).mpr (fun a _ => HU a)
  filter_upwards [HT] with t ht
  intro x p hp
  have hx : (x,riemannianExp x p)∈ ⋃ a∈S,U a := by rw [hS]; trivial
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp hx
  apply (ht a ha x p hxa hp).trans
  calc
    C a≤|C a| := le_abs_self _
    _≤∑ z∈S, |C z| := Finset.single_le_sum (fun z _ => abs_nonneg (C z)) ha
    _≤B := le_add_of_nonneg_left zero_le_one

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_UniformReverseGain
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

lemma exists_uniform_reverse_divided_gain :
    ∃ c>0, ∀ᶠ z : ℝ×ℝ in 𝓝 (1,1), z.1≤z.2 → z.2<1 →
      ∀ x y : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      ∀ q : TangentSpace 𝓘(ℝ,Model n) y,
      p∈minimizingVectors x → q∈injectivityDomain y →
      riemannianExp x (z.1 • p)=y → riemannianExp y q=x →
      ∃ R : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x,
        ContDiffAt ℝ ∞ R q ∧ R q=0 ∧
        (∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w) ∧
        ∀ w : TangentSpace 𝓘(ℝ,Model n) y,
          c*(z.2-z.1)*‖w‖^2 ≤
            hessianValue x (z.1 • p) (fderiv ℝ R q w)/z.1-
              hessianValue x (z.2 • p) (fderiv ℝ R q w)/z.2 := by
  obtain ⟨h,hh,hh1,Hsplit⟩ := exists_actual_uniform_regular_split (n := n) (M := M)
  obtain ⟨c,hc,C,hC,HC⟩ := fixedJoinMiddle_uniform_interval_crossing hh hh1 Hsplit
  obtain ⟨B,hB,HB⟩ := normalEndpointMixedOperator_uniform_bound hh hh1 Hsplit
  have Hnear : Tendsto (fun z : ℝ×ℝ => h/z.1) (𝓝 (1,1)) (𝓝 h) := by
    have H : ContinuousAt (fun z : ℝ×ℝ => h/z.1) (1,1) :=
      continuousAt_const.div continuousAt_fst (by norm_num)
    simpa only [div_one] using H.tendsto
  have Hpos : ∀ᶠ z : ℝ×ℝ in 𝓝 (1,1), h<z.1 :=
    continuousAt_fst.eventually (eventually_gt_nhds hh1)
  refine ⟨c/B^2,div_pos hc (sq_pos_of_pos hB),?_⟩
  filter_upwards [HC,Hnear.eventually HB,Hpos] with z hz hnorm hhs
  intro hst ht1 x y p q hp hq hpx hqy
  have hs : 0<z.1 := hh.trans hhs
  have ht : 0<z.2 := hs.trans_le hst
  have hs1 : z.1<1 := hst.trans_lt ht1
  have hps := contracted_minimizer_mem_injectivityDomain hp hs hs1
  have hpt := contracted_minimizer_mem_injectivityDomain hp ht ht1
  have hbound : z.1*‖normalEndpointMixedOperator x y (h/z.1) (z.1 • p)‖≤B := by
    have H := hnorm x (z.1 • p) (injectivityDomain_subset_minimizingVectors x hps)
    rw [hpx] at H
    calc
      _ ≤ 1*‖normalEndpointMixedOperator x y (h/z.1) (z.1 • p)‖ := by
        gcongr
      _ ≤ B := by simpa only [one_mul] using H
  obtain ⟨R,hR,hR0,hRi,HR⟩ := exists_reverse_exp_divided_isotropic_gain hh hhs
    (hhs.trans_le hst) hps hpt hq hpx hqy hB
    (mul_nonneg hc.le (sub_nonneg.mpr hst))
    (fun v => (hz hhs ht1 hst x p hp v).1) hbound
  refine ⟨R,hR,hR0,hRi,?_⟩
  intro w
  convert HR w using 1
  all_goals try with_reducible_and_instances rfl
  ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_UniformJacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exp_mfderiv_zero_apply (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) 0 v=v := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have heq : (fun t : ℝ => riemannianExp x (t • v))=
      (fun t : ℝ => (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :=
    funext (riemannianExp_smul x v)
  have hf : HasFDerivAt (fun t : ℝ => t • v) ((1 : ℝ →L[ℝ] ℝ).smulRight v) 0 :=
    ((1 : ℝ →L[ℝ] ℝ).smulRight v).hasFDerivAt
  have H := mfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,V))
    (I'' := 𝓘(ℝ,Model n)) (0:ℝ)
    ((contMDiff_riemannianExp_fiber x (0 • v)).mdifferentiableAt (by simp))
    hf.differentiableAt.mdifferentiableAt (1:ℝ)
  have hv := spray_velocity_eq_mfderiv ((sprayFlow_curve
    (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).isMIntegralCurveAt (0:ℝ))
  simp only [Function.comp_def,mfderiv_eq_fderiv,hf.fderiv] at H
  rw [heq] at H
  rw [sprayFlow_zero] at hv
  have hz : (0:ℝ) • v=(0:V) := zero_smul ℝ v
  have h1 : ((1 : ℝ →L[ℝ] ℝ).smulRight v) (1:ℝ)=v := by simp
  erw [hz,h1] at H
  exact H.symm.trans hv

end WeakMTWTransport

end



noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.tangentFiniteExpJac
lemma normal_endpoint_derivative_eq {x y : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hL : DifferentiableAt ℝ L p) (hLp : L p=0)
    (hLi : ∀ᶠ v in 𝓝 p, riemannianExp y (L v)=riemannianExp x v)
    (k : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ L p k=mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) p k := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let W := TangentSpace 𝓘(ℝ,Model n) y
  have H := mfderiv_comp_apply_of_eq (I := 𝓘(ℝ,V)) (I' := 𝓘(ℝ,W))
    (I'' := 𝓘(ℝ,Model n)) p
    ((contMDiff_riemannianExp_fiber y 0).mdifferentiableAt (by simp))
    hL.mdifferentiableAt hLp k
  erw [mfderiv_eq_fderiv,exp_mfderiv_zero_apply] at H
  have HC := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ,V)) (I' := 𝓘(ℝ,Model n))
    (show riemannianExp y ∘ L =ᶠ[𝓝 p] riemannianExp x from hLi)
  have HC' := congrArg (fun A => A k) HC
  exact H.symm.trans HC'

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_TrueCenterGain
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

lemma regular_divided_hessian_decrease {y:M} {p d:TangentSpace 𝓘(ℝ,Model n) y}
    (hp:p∈injectivityDomain y) {s:ℝ} (hs:0 < s) (hs1:s<1) :
    hessianValue y p d ≤ hessianValue y (s • p) d/s := by
  by_cases hd:d=0
  · subst d
    rw [hessianValue_eq_normalHessian hp,hessianValue_eq_normalHessian
      (contracted_minimizer_mem_injectivityDomain
        (injectivityDomain_subset_minimizingVectors y hp) hs hs1)]
    simp
  · exact (hessianValue_strict_radial_decrease hp hs hs1 hd).le

lemma exists_uniform_true_center_gain_oai :
    ∃c>0,∀ᶠ l:ℝ in 𝓝 1,l<1 → ∀x:M,∀q:TangentSpace 𝓘(ℝ,Model n) x,
    ∀p:TangentSpace 𝓘(ℝ,Model n) (riemannianExp x q),
      p∈injectivityDomain (riemannianExp x q) → q∈injectivityDomain x →
      riemannianExp (riemannianExp x q) (l • p)=x →
      ∀R:TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x q),
      DifferentiableAt ℝ R q → R q=0 →
      (∀ᶠ z in 𝓝 q,riemannianExp (riemannianExp x q) (R z)=riemannianExp x z) →
      ∀d,c*(1-l)*‖d‖^2 ≤
        normalHessian (riemannianExp x q) (l • p) (fderiv ℝ R q d) (fderiv ℝ R q d)-
        l*normalHessian (riemannianExp x q) p (fderiv ℝ R q d) (fderiv ℝ R q d) := by
  obtain ⟨c,hc,H⟩:=exists_uniform_reverse_divided_gain (n:=n) (M:=M)
  have hpair:Tendsto (fun l:ℝ=>(l,(1+l)/2)) (𝓝 1) (𝓝 (1,1)):=by
    have hh:ContinuousAt (fun l:ℝ=>(l,(1+l)/2)) (1:ℝ):=
      continuousAt_id.prodMk ((continuousAt_const.add continuousAt_id).div_const 2)
    simpa using hh.tendsto
  refine ⟨c/4,by positivity,?_⟩
  filter_upwards [hpair.eventually H,eventually_gt_nhds (by norm_num : (1/2:ℝ)<1)] with l hl hhalf
  intro hl1 x q p hp hq hpx R hR hR0 hRe d
  have hl0:0<l:=by linarith
  have hs0:0<(1+l)/2:=by positivity
  have hs1:(1+l)/2<1:=by linarith
  have hls:l≤(1+l)/2:=by linarith
  have hpm:=injectivityDomain_subset_minimizingVectors _ hp
  obtain ⟨S,hS,hS0,hSe,HS⟩:=hl hls hs1 (riemannianExp x q) x p q hpm hq hpx rfl
  have hder:fderiv ℝ S q=fderiv ℝ R q:=by
    ext w
    rw [normal_endpoint_derivative_eq (hS.differentiableAt (by simp)) hS0 hSe,
      normal_endpoint_derivative_eq hR hR0 hRe]
  rw [hder] at HS
  have HA:=regular_divided_hessian_decrease hp hs0 hs1 (d:=fderiv ℝ R q d)
  have HD:=mul_le_mul_of_nonneg_left (HS d) hl0.le
  have HE:l*(hessianValue (riemannianExp x q) (l • p) (fderiv ℝ R q d)/l-
      hessianValue (riemannianExp x q) (((1+l)/2) • p) (fderiv ℝ R q d)/((1+l)/2))=
      hessianValue (riemannianExp x q) (l • p) (fderiv ℝ R q d)-
      l*(hessianValue (riemannianExp x q) (((1+l)/2) • p) (fderiv ℝ R q d)/((1+l)/2)):=by
    field_simp
  rw [HE] at HD
  have HG:(c/4)*(1-l)*‖d‖^2 ≤ l*(c*((1+l)/2-l)*‖d‖^2):=by
    nlinarith only [mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hl1.le)) (sq_nonneg ‖d‖),
      mul_nonneg (sub_nonneg.mpr hhalf.le)
        (mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hl1.le)) (sq_nonneg ‖d‖))]
  have HT:=mul_le_mul_of_nonneg_left HA hl0.le
  rw [hessianValue_eq_normalHessian hp] at HT
  rw [hessianValue_eq_normalHessian
    (contracted_minimizer_mem_injectivityDomain hpm hl0 hl1)] at HD
  linarith only [HD,HG,HT]
end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.exists_uniform_true_center_gain_oai.{u_1} := @OAI.WeakMTWTransport.exists_uniform_true_center_gain_oai.{u_1}
