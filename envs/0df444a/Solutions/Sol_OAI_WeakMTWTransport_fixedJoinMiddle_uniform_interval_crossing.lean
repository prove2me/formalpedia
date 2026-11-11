-- Prove2me | solution 1 for OAI.WeakMTWTransport.fixedJoinMiddle_uniform_interval_crossing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:18:48.931265+00:00
-- url     : https://prove2.me/submissions/d9a4b5b5-12bf-4cda-83a6-765e77b8b748

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
import Definitions.Def_OAIQ232A024
import Theorems.Thm_OAI_WeakMTWTransport_movingFixedJoinMiddle_strict_crossing

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FixedJoinSmooth
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

lemma shifted_exp_time (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) (h T : ℝ) :
    riemannianExp (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
      ((T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2)=
      riemannianExp x (T • p) := by
  rw [riemannianExp_eq_sprayFlow]
  change (sprayFlow 1 (tangentScale (T-h) (sprayFlow h ⟨x,p⟩))).1=_
  rw [sprayFlow_scale,mul_one,←sprayFlow_add,sub_add_cancel,riemannianExp_smul]
  rfl

lemma fixedJoinAction_joint_contDiffAt {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hTh : T≠h)
    (hleft : h • p∈injectivityDomain x)
    (hright : (T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (TangentSpace 𝓘(ℝ,Model n) x ×
      (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x)) =>
      fixedJoinAction x h q.1 q.2.1 q.2.2) (T,(p,(0,p))) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let a : ℝ × (V×(V×V)) := (T,(p,(0,p)))
  have he := contMDiff_riemannianExp_fiber (n := n) x
  have hu : ContMDiffAt 𝓘(ℝ,ℝ×(V×(V×V))) 𝓘(ℝ,Model n) ∞
      (fun q : ℝ×(V×(V×V)) => riemannianExp x q.2.2.1) a :=
    (he _).comp a (show ContDiffAt ℝ ∞ (fun q : ℝ×(V×(V×V)) => q.2.2.1) a from by fun_prop).contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,ℝ×(V×(V×V))) 𝓘(ℝ,Model n) ∞
      (fun q : ℝ×(V×(V×V)) => riemannianExp x (h • q.2.2.2)) a :=
    (he _).comp a (show ContDiffAt ℝ ∞ (fun q : ℝ×(V×(V×V)) => h • q.2.2.2) a from by fun_prop).contMDiffAt
  have hw : ContMDiffAt 𝓘(ℝ,ℝ×(V×(V×V))) 𝓘(ℝ,Model n) ∞
      (fun q : ℝ×(V×(V×V)) => riemannianExp x (q.1 • q.2.1)) a :=
    (he _).comp a (show ContDiffAt ℝ ∞ (fun q : ℝ×(V×(V×V)) => q.1 • q.2.1) a from by fun_prop).contMDiffAt
  have hc₁ := cost_contMDiffAt_of_injectivityDomain
    (⟨x,h • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hleft
  have hc₂ := cost_contMDiffAt_of_injectivityDomain
    (⟨(sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      (T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hright
  have hc₁' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:V),riemannianExp x (h • p)) := by
    simpa only [riemannianExp_zero] using hc₁
  have hc₂' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (h • p),riemannianExp x (T • p)) := by
    dsimp only at hc₂
    rw [shifted_exp_time] at hc₂
    simpa only [riemannianExp_smul] using hc₂
  exact ((hc₁'.comp a (hu.prodMk hv)).contDiffAt.div_const h).add
    (((hc₂'.comp a (hv.prodMk hw)).contDiffAt).div
      (contDiffAt_fst.sub contDiffAt_const) (sub_ne_zero.mpr hTh))

lemma fixedJoinAction_contDiffAt {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hTh : T≠h)
    (hleft : h • p∈injectivityDomain x)
    (hright : (T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (fixedJoinAction x h T p) (0,p) := by
  exact (fixedJoinAction_joint_contDiffAt hTh hleft hright).comp (0,p)
    (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))

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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CompactCrossing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bilinear_lower_of_unit (L : E →L[ℝ] E →L[ℝ] ℝ) {c : ℝ}
    (h : ∀ v:E, ‖v‖=1 → c ≤ L v v) (v:E) : c*‖v‖^2 ≤ L v v := by
  by_cases hv : v=0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖=1 := by simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have he : v=‖v‖ • w := by dsimp [w]; rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  have H := mul_le_mul_of_nonneg_left (h w hw) (sq_nonneg ‖v‖)
  calc
    c*‖v‖^2 = ‖v‖^2*c := mul_comm _ _
    _ ≤ ‖v‖^2*L w w := H
    _ = L (‖v‖ • w) (‖v‖ • w) := by simp only [map_smul,smul_apply,smul_eq_mul] <;> ring
    _ = L v v := by rw [←he]

lemma bilinear_diag_abs_le (L : E →L[ℝ] E →L[ℝ] ℝ) (v:E) :
    |L v v| ≤ ‖L‖*‖v‖^2 := by
  calc
    |L v v| = ‖L v v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖L v‖*‖v‖ := (L v).le_opNorm _
    _ ≤ (‖L‖*‖v‖)*‖v‖ := mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)
    _ = ‖L‖*‖v‖^2 := by ring

lemma bilinear_time_hasDerivAt {H : ℝ×Q → E →L[ℝ] E →L[ℝ] ℝ}
    {t:ℝ} {q:Q} (hH : DifferentiableAt ℝ H (t,q)) (v:E) :
    HasDerivAt (fun s => H (s,q) v v) (fderiv ℝ H (t,q) (1,0) v v) t := by
  have hp : HasDerivAt (fun s : ℝ => (s,q)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t q)
  have HD : HasDerivAt (fun s : ℝ => H (s,q)) (fderiv ℝ H (t,q) (1,0)) t :=
    HasFDerivAt.comp_hasDerivAt (l := H) (l' := fderiv ℝ H (t,q))
      (f := fun s : ℝ => (s,q)) t hH.hasFDerivAt hp
  have HV := (HD.clm_apply (hasDerivAt_const t v)).clm_apply (hasDerivAt_const t v)
  simpa only [Function.comp_def,map_zero,add_zero,zero_add] using HV
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_InverseProfile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

variable [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteJoin_r64e3e7_1 (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma fixedJoinAction_shortened_contDiffAt {x : M} {h T:ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hh1 : h < 1) (hT : h < T) (hT1 : T < 1)
    (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (fixedJoinAction x h T p) (0,p) := by
  have hden : 0 < 1-h := sub_pos.mpr hh1
  have ht0 : 0 < (T-h)/(1-h) := div_pos (sub_pos.mpr hT) hden
  have ht1 : (T-h)/(1-h) < 1 := (div_lt_one hden).mpr (by linarith)
  have H := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors _ hright) ht0 ht1
  rw [smul_smul,div_mul_cancel₀ _ hden.ne'] at H
  exact fixedJoinAction_contDiffAt hT.ne' hleft H
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FixedJoinUpper
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

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma movingFixedJoinAction_eq {a : M} {b : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (h T : ℝ) (p z : Model n) :
    movingFixedJoinAction a h (T,(b,p)) z=
      fixedJoinAction ((extChartAt 𝓘(ℝ,Model n) a).symm b) h T
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p)
      (0,((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p)+
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) z)) := by
  simp only [movingFixedJoinAction,fixedJoinAction,movingNormal_eq hb,map_smul,map_add,map_zero]

lemma movingFixedJoinAction_contDiffAt {a : M} {b p : Model n} {h T : ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hTh : T≠h)
    (hleft : h • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hright : (T-h) • (sprayFlow h
      (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
        (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h
        (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
          (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
            ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingFixedJoinAction a h)) ((T,(b,p)),0) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  let q := ((T,(b,p)),(0 : Model n))
  let Q := (ℝ×(Model n×Model n))×Model n
  have hA : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun z : Q => movingNormal a (z.1.2.1,0)) q :=
    (movingNormal_contMDiffAt (q := (b,0)) hb).comp q
      (contDiffAt_fst.snd.fst.prodMk contDiffAt_const).contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun z : Q => movingNormal a (z.1.2.1,h • (z.1.2.2+z.2))) q :=
    (movingNormal_contMDiffAt (q := (b,h • (p+0))) hb).comp q
      (contDiffAt_fst.snd.fst.prodMk
        ((contDiffAt_const (c := h)).smul (contDiffAt_fst.snd.snd.add contDiffAt_snd))).contMDiffAt
  have hC : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun z : Q => movingNormal a (z.1.2.1,z.1.1 • z.1.2.2)) q :=
    (movingNormal_contMDiffAt (q := (b,T • p)) hb).comp q
      (contDiffAt_fst.snd.fst.prodMk
        (contDiffAt_fst.fst.smul contDiffAt_fst.snd.snd)).contMDiffAt
  have hc₁ := cost_contMDiffAt_of_injectivityDomain
    (⟨x,h • L p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hleft
  have hc₂ := cost_contMDiffAt_of_injectivityDomain
    (⟨(sprayFlow h (⟨x,L p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      (T-h) • (sprayFlow h (⟨x,L p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hright
  have hc₁' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => cost z.1 z.2)
      (movingNormal a (b,0),movingNormal a (b,h • (p+0))) := by
    simpa only [movingNormal_eq hb,map_zero,riemannianExp_zero,add_zero,map_smul] using hc₁
  have hc₂' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => cost z.1 z.2)
      (movingNormal a (b,h • (p+0)),movingNormal a (b,T • p)) := by
    dsimp only at hc₂
    rw [shifted_exp_time] at hc₂
    simpa only [movingNormal_eq hb,add_zero,map_smul,riemannianExp_smul] using hc₂
  exact ((hc₁'.comp q (hA.prodMk hB)).contDiffAt.div_const h).add
    (((hc₂'.comp q (hB.prodMk hC)).contDiffAt).div
      (contDiffAt_fst.fst.sub contDiffAt_const) (sub_ne_zero.mpr hTh))

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma movingFixedJoinMiddle_contDiffAt {a : M} {h T : ℝ} {b p : Model n}
    (H : ContDiffAt ℝ ∞ (Function.uncurry (movingFixedJoinAction a h)) ((T,(b,p)),0)) :
    ContDiffAt ℝ ∞ (movingFixedJoinMiddle a h) (T,(b,p)) :=
  (ContDiffAt.partial_snd_fderiv_two H).comp (T,(b,p))
    (contDiffAt_id.prodMk contDiffAt_const)

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma movingFixedJoinMiddle_eq {a : M} {b : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (h T : ℝ) (p v w : Model n)
    (H : ContDiffAt ℝ 2 (fixedJoinAction ((extChartAt 𝓘(ℝ,Model n) a).symm b) h T
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p))
      (0,((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p))) :
    movingFixedJoinMiddle a h (T,(b,p)) v w=
      fixedJoinMiddle ((extChartAt 𝓘(ℝ,Model n) a).symm b) h T
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p)
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) v)
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) w) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  let I := (0 : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x).prod L
  have he : movingFixedJoinAction a h (T,(b,p))=
      (fun z => fixedJoinAction x h T (L p) ((0,L p)+I z)) := by
    ext z
    simpa only [I,ContinuousLinearMap.prod_apply,zero_apply,
      Prod.mk_add_mk,add_zero] using movingFixedJoinAction_eq hb h T p z
  rw [movingFixedJoinMiddle,he]
  have H' := second_fderiv_comp_affine I (0,L p) 0 (by simpa only [map_zero,add_zero] using H) v w
  simpa only [I,ContinuousLinearMap.prod_apply,zero_apply,map_zero,
    add_zero,fixedJoinMiddle_apply] using H'

lemma movingFixedJoinMiddle_trivialization {a x : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source) (h T : ℝ)
    (p v w : TangentSpace 𝓘(ℝ,Model n) x)
    (H : ContDiffAt ℝ 2 (fixedJoinAction x h T p) (0,p)) :
    movingFixedJoinMiddle a h (T,(extChartAt 𝓘(ℝ,Model n) a x,
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p))
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x v)
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x w)=
        fixedJoinMiddle x h T p v w := by
  let e := trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  have hx' : x∈e.baseSet := by simpa only [e,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
  have HL : ∀ v : TangentSpace 𝓘(ℝ,Model n) x, e.symmL ℝ x (e.continuousLinearMapAt ℝ x v)=v :=
    fun v => e.symmL_continuousLinearMapAt hx' v
  have HB : ContDiffAt ℝ 2
    (fixedJoinAction ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a x)) h T
      (e.symmL ℝ ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a x))
        (e.continuousLinearMapAt ℝ x p)))
    (0,e.symmL ℝ ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a x))
      (e.continuousLinearMapAt ℝ x p)) := by
    rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv hx,HL]
    exact H
  have HE := movingFixedJoinMiddle_eq ((extChartAt 𝓘(ℝ,Model n) a).map_source hx) h T
    (e.continuousLinearMapAt ℝ x p) (e.continuousLinearMapAt ℝ x v)
    (e.continuousLinearMapAt ℝ x w) HB
  dsimp only [e] at HL HE
  rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv hx] at HE
  simpa only [HL] using HE

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_UniformExpJacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_bilinear_interval_crossing {K : Set Q} (hK : IsCompact K)
    {H : ℝ×Q → E →L[ℝ] E →L[ℝ] ℝ}
    (hH : ∀ q∈K, ContDiffAt ℝ ∞ H (1,q))
    (hneg : ∀ q∈K, ∀ v:E, ‖v‖=1 → 0 < -(fderiv ℝ H (1,q) (1,0) v v)) :
    ∃ c > 0, ∃ C > 0, ∃ ε > 0,
      ∀ s t : ℝ, s∈ball 1 ε → t∈ball 1 ε → s≤t → ∀ q∈K, ∀ v:E,
      c*(t-s)*‖v‖^2 ≤ H (s,q) v v-H (t,q) v v ∧
      H (s,q) v v-H (t,q) v v ≤ C*(t-s)*‖v‖^2 := by
  let J : ℝ×Q → E →L[ℝ] E →L[ℝ] ℝ := fun z => fderiv ℝ H z (1,0)
  have hJ : ∀ q∈K, ContinuousAt J (1,q) := by
    intro q hq
    exact ((hH q hq).continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply continuousAt_const
  let S : Set (Q×E) := K ×ˢ sphere (0:E) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  let F : ℝ×(Q×E) → ℝ := fun z => -(J (z.1,z.2.1) z.2.2 z.2.2)
  have hF : ∀ z∈S, ContinuousAt F (1,z) := by
    intro z hz
    exact ((((hJ z.1 hz.1).comp (x := (1,z))
      (continuousAt_fst.prodMk continuousAt_snd.fst)).clm_apply
        continuousAt_snd.snd).clm_apply continuousAt_snd.snd).neg
  have hFc : ContinuousOn (fun z => F (1,z)) S := by
    intro z hz
    exact ((hF z hz).comp (x := z) (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨c,hc,HS⟩ : ∃ c>0, ∀ z∈S, c < F (1,z) := by
    by_cases hne : S.Nonempty
    · obtain ⟨z,hz,hmin⟩ := hS.exists_isMinOn hne hFc
      have hp : 0 < F (1,z) := hneg z.1 hz.1 z.2
        (by simpa only [mem_sphere,dist_zero_right] using hz.2)
      exact ⟨F (1,z)/2,half_pos hp,fun y hy => (half_lt_self hp).trans_le (hmin hy)⟩
    · exact ⟨1,zero_lt_one,fun z hz => (hne ⟨z,hz⟩).elim⟩
  have HF : ∀ᶠ t in 𝓝 (1:ℝ), ∀ z∈S, c < F (t,z) :=
    hS.eventually_forall_of_forall_eventually (fun z hz =>
      (continuousAt_const.eventually_lt (hF z hz) (HS z hz)))
  obtain ⟨C,hC,HC⟩ := compact_eventually_fiberwise_bound hK
    (f := fun _ : Q => ()) continuous_const (g := fun _ : ℝ => ())
    (continuousAt_const (x := 1)) (h := J) (fun q hq _ => hJ q hq)
  have HD : ∀ᶠ t in 𝓝 (1:ℝ), ∀ q∈K, DifferentiableAt ℝ H (t,q) :=
    hK.eventually_forall_of_forall_eventually (fun q hq =>
      (((hH q hq).of_le (m := 1) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mono (fun z hz => hz.differentiableAt (by norm_num)))
  obtain ⟨ε,hε,Hε⟩ := Metric.mem_nhds_iff.mp (HF.and (HC.and HD))
  refine ⟨c,hc,C,hC,ε,hε,?_⟩
  intro t₀ t₁ ht₀ ht₁ htt q hq v
  have hall : ∀ s∈Icc t₀ t₁,
      DifferentiableAt ℝ (fun s => H (s,q) v v) s ∧
      deriv (fun s => H (s,q) v v) s ≤ -c*‖v‖^2 ∧
      -C*‖v‖^2 ≤ deriv (fun s => H (s,q) v v) s := by
    intro s hs
    have hsb : s∈ball (1:ℝ) ε := by
      rw [mem_ball,Real.dist_eq,abs_lt] at ht₀ ht₁ ⊢
      constructor <;> linarith only [ht₀.1,ht₀.2,ht₁.1,ht₁.2,hs.1,hs.2]
    have HE := Hε hsb
    have HDs := bilinear_time_hasDerivAt (HE.2.2 q hq) v
    refine ⟨HDs.differentiableAt,?_,?_⟩
    · rw [HDs.deriv]
      have HL := bilinear_lower_of_unit (-J (s,q)) (c := c) (by
        intro w hw
        have H := (HE.1 (q,w) ⟨hq,by simpa only [mem_sphere,dist_zero_right] using hw⟩).le
        exact H) v
      change c*‖v‖^2 ≤ -(J (s,q) v v) at HL
      change J (s,q) v v ≤ -c*‖v‖^2
      linarith only [HL]
    · rw [HDs.deriv]
      have HL := (bilinear_diag_abs_le (J (s,q)) v).trans
        (mul_le_mul_of_nonneg_right (HE.2.1 q hq rfl) (sq_nonneg ‖v‖))
      have HL' := (abs_le.mp HL).1
      change -C*‖v‖^2 ≤ J (s,q) v v
      linarith only [HL']
  have Hcont : ContinuousOn (fun s => H (s,q) v v) (Icc t₀ t₁) :=
    fun s hs => (hall s hs).1.continuousAt.continuousWithinAt
  have HDiff : DifferentiableOn ℝ (fun s => H (s,q) v v) (interior (Icc t₀ t₁)) :=
    fun s hs => (hall s (interior_subset hs)).1.differentiableWithinAt
  have HU := (convex_Icc t₀ t₁).image_sub_le_mul_sub_of_deriv_le Hcont HDiff
    (fun s hs => (hall s (interior_subset hs)).2.1) t₀ ⟨le_rfl,htt⟩ t₁ ⟨htt,le_rfl⟩ htt
  have HL := (convex_Icc t₀ t₁).mul_sub_le_image_sub_of_le_deriv Hcont HDiff
    (fun s hs => (hall s (interior_subset hs)).2.2) t₀ ⟨le_rfl,htt⟩ t₁ ⟨htt,le_rfl⟩ htt
  constructor <;> nlinarith only [HU,HL]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_UniformIntervalCrossing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

lemma fixedJoinMiddle_interval_crossing_near_base {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (Hsplit : ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      h • p∈injectivityDomain x ∧
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) (a : M) :
    ∃ c > 0, ∃ C > 0, ∃ K∈𝓝 a, ∀ᶠ z in 𝓝 ((1:ℝ),(1:ℝ)), h < z.1 → z.2 < 1 → z.1 ≤ z.2 →
      ∀ x∈K, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      ∀ k : TangentSpace 𝓘(ℝ,Model n) x,
        c*(z.2-z.1)*‖k‖^2 ≤ fixedJoinMiddle x h z.1 p k k-fixedJoinMiddle x h z.2 p k k ∧
        fixedJoinMiddle x h z.1 p k k-fixedJoinMiddle x h z.2 p k k ≤ C*(z.2-z.1)*‖k‖^2 := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨B,hBpos,hB⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) a
  obtain ⟨D,hDpos,hD⟩ := eventually_norm_symmL_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) a
  obtain ⟨K,hKn,hKs,hKc⟩ := local_compact_nhds
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a) (inter_mem hB hD))
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let e := trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  let P := minimizingChartParameters (n := n) a K
  have HP : ∀ q∈P, q.1∈χ.target ∧
      h • e.symmL ℝ (χ.symm q.1) q.2∈injectivityDomain (χ.symm q.1) ∧
      (1-h) • (sprayFlow h (⟨χ.symm q.1,e.symmL ℝ (χ.symm q.1) q.2⟩ :
        TangentBundle 𝓘(ℝ,Model n) M)).2∈injectivityDomain
        (sprayFlow h (⟨χ.symm q.1,e.symmL ℝ (χ.symm q.1) q.2⟩ :
          TangentBundle 𝓘(ℝ,Model n) M)).1 := by
    intro q hq
    have H := mem_minimizingChartParameters (fun x hx => (hKs hx).1) hq
    exact ⟨H.1,Hsplit _ _ H.2.2⟩
  obtain ⟨c,hc,C,hC,ε,hε,HC⟩ := compact_bilinear_interval_crossing
    (isCompact_minimizingChartParameters hKc (fun x hx => (hKs hx).1))
    (H := movingFixedJoinMiddle a h)
    (fun q hq => movingFixedJoinMiddle_contDiffAt
      (movingFixedJoinAction_contDiffAt (HP q hq).1 hh1.ne' (HP q hq).2.1 (HP q hq).2.2))
    (fun q hq v hv => movingFixedJoinMiddle_strict_crossing (HP q hq).1 hh hh1
      (HP q hq).2.1 (HP q hq).2.2 v hv)
  refine ⟨c/D^2,div_pos hc (sq_pos_of_pos hDpos),C*B^2,
    mul_pos hC (sq_pos_of_pos hBpos),K,hKn,?_⟩
  have Hz₁ : ∀ᶠ z : ℝ×ℝ in 𝓝 (1,1), z.1∈Metric.ball 1 ε :=
    continuousAt_fst.eventually (Metric.ball_mem_nhds 1 hε)
  have Hz₂ : ∀ᶠ z : ℝ×ℝ in 𝓝 (1,1), z.2∈Metric.ball 1 ε :=
    continuousAt_snd.eventually (Metric.ball_mem_nhds 1 hε)
  filter_upwards [Hz₁,Hz₂] with z hz₁ hz₂
  intro hhT hT1 hzle x hx p hp k
  let A := e.continuousLinearMapAt ℝ x
  have hxp : (χ x,A p)∈P :=
    trivialization_mem_minimizingChartParameters (fun x hx => (hKs hx).1) hx hp
  have HE := HC z.1 z.2 hz₁ hz₂ hzle (χ x,A p) hxp (A k)
  have HS := Hsplit x p hp
  have HB1 := (fixedJoinAction_shortened_contDiffAt hh1 (hhT.trans_le hzle) hT1 HS.1 HS.2).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HBT := (fixedJoinAction_shortened_contDiffAt hh1 hhT (hzle.trans_lt hT1) HS.1 HS.2).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [movingFixedJoinMiddle_trivialization (hKs hx).1 h z.1 p k k HBT,
    movingFixedJoinMiddle_trivialization (hKs hx).1 h z.2 p k k HB1] at HE
  have hbase : x∈e.baseSet := by
    simpa only [e,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (hKs hx).1
  have hA : ‖A k‖ ≤ B*‖k‖ :=
    (A.le_opNorm k).trans (mul_le_mul_of_nonneg_right (hKs hx).2.1.le (norm_nonneg _))
  have hL : ‖k‖ ≤ D*‖A k‖ := by
    calc
      ‖k‖ = ‖e.symmL ℝ x (A k)‖ := by rw [Trivialization.symmL_continuousLinearMapAt e hbase]
      _ ≤ ‖e.symmL ℝ x‖*‖A k‖ := (e.symmL ℝ x).le_opNorm _
      _ ≤ D*‖A k‖ := mul_le_mul_of_nonneg_right (hKs hx).2.2.le (norm_nonneg _)
  have hL2 : ‖k‖^2 ≤ D^2*‖A k‖^2 := by nlinarith only [hL,sq_nonneg (‖k‖-D*‖A k‖),norm_nonneg k,mul_nonneg hDpos.le (norm_nonneg (A k))]
  have hA2 : ‖A k‖^2 ≤ B^2*‖k‖^2 := by nlinarith only [hA,sq_nonneg (‖A k‖-B*‖k‖),norm_nonneg (A k),mul_nonneg hBpos.le (norm_nonneg k)]
  constructor
  · calc
      (c/D^2)*(z.2-z.1)*‖k‖^2 ≤ (c/D^2)*(z.2-z.1)*(D^2*‖A k‖^2) := by gcongr
      _ = c*(z.2-z.1)*‖A k‖^2 := by field_simp
      _ ≤ _ := HE.1
  · calc
      _ ≤ C*(z.2-z.1)*‖A k‖^2 := HE.2
      _ ≤ C*(z.2-z.1)*(B^2*‖k‖^2) := by gcongr
      _ = (C*B^2)*(z.2-z.1)*‖k‖^2 := by ring

lemma fixedJoinMiddle_uniform_interval_crossing_oai {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (Hsplit : ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      h • p∈injectivityDomain x ∧
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∃ c > 0, ∃ C > 0, ∀ᶠ z in 𝓝 ((1:ℝ),(1:ℝ)), h < z.1 → z.2 < 1 → z.1 ≤ z.2 →
      ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      ∀ k : TangentSpace 𝓘(ℝ,Model n) x,
        c*(z.2-z.1)*‖k‖^2 ≤ fixedJoinMiddle x h z.1 p k k-fixedJoinMiddle x h z.2 p k k ∧
        fixedJoinMiddle x h z.1 p k k-fixedJoinMiddle x h z.2 p k k ≤ C*(z.2-z.1)*‖k‖^2 := by
  classical
  choose c hc C hC K hKn hK using fixedJoinMiddle_interval_crossing_near_base hh hh1 Hsplit
  obtain ⟨s,hs⟩ := finite_cover_nhds hKn
  have hlow : ∃ b > 0, ∀ a∈s, b ≤ c a := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨b,hb,Hb⟩ := ih
      refine ⟨min b (c a),lt_min hb (hc a),?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl|hz
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (Hb z hz)
  have hupp : ∃ b > 0, ∀ a∈s, C a ≤ b := by
    clear hs hlow
    induction s using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨b,hb,Hb⟩ := ih
      refine ⟨max b (C a),hb.trans_le (le_max_left _ _),?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl|hz
      · exact le_max_right _ _
      · exact (Hb z hz).trans (le_max_left _ _)
  obtain ⟨b,hb,Hb⟩ := hlow
  obtain ⟨B,hB,HB⟩ := hupp
  refine ⟨b,hb,B,hB,?_⟩
  have HT := (eventually_all_finset s).mpr (fun a _ => hK a)
  filter_upwards [HT] with z hT
  intro hhT hT1 hzle x p hp k
  have hx : x∈ ⋃ a∈s,K a := by rw [hs]; trivial
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp hx
  have H := hT a ha hhT hT1 hzle x hxa p hp k
  refine ⟨le_trans ?_ H.1,le_trans H.2 ?_⟩
  · gcongr; exact Hb a ha
  · gcongr; exact HB a ha

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.fixedJoinMiddle_uniform_interval_crossing_oai.{u_1} := @OAI.WeakMTWTransport.fixedJoinMiddle_uniform_interval_crossing_oai.{u_1}
