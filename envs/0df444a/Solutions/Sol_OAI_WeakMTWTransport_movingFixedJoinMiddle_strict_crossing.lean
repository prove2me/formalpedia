-- Prove2me | solution 1 for OAI.WeakMTWTransport.movingFixedJoinMiddle_strict_crossing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:18:50.012866+00:00
-- url     : https://prove2.me/submissions/a1e7921e-f3bd-4748-8fc3-bca7aefa9f39

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
import Theorems.Thm_OAI_WeakMTWTransport_exists_fixedJoinMiddle_lower_crossing

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_DerivativeNegLowerCrossing
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

lemma derivative_neg_of_lower_crossing {f : ℝ → ℝ} {d a c : ℝ}
    (hd : HasDerivAt f d 1) (ha : a < 1) (hc : 0 < c)
    (hf : ∀ᶠ t in 𝓝 (1:ℝ), a < t → t < 1 → c*(1-t) ≤ f t-f 1) : 0 < -d := by
  have Hsl : Tendsto (slope f 1) (𝓝[<] (1:ℝ)) (𝓝 d) :=
    hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE 1)
  have Hle : ∀ᶠ t in 𝓝[<] (1:ℝ), slope f 1 t ≤ -c := by
    filter_upwards [hf.filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds ha).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht hat ht1
    have H := ht hat ht1
    rw [slope_def_field]
    exact (div_le_iff_of_neg (sub_neg.mpr ht1)).mpr (by nlinarith only [H])
  have H := le_of_tendsto Hsl Hle
  linarith only [H,hc]

end WeakMTWTransport

end

end OAI
end

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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CompactCrossing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

local instance tangentFiniteJoin_rb99c53_1 (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
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

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MovingCrossing
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

lemma movingFixedJoinMiddle_strict_crossing_oai {a : M} {b p : Model n} {h : ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hh : 0 < h) (hh1 : h < 1)
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
            ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) (v : Model n) (hv : ‖v‖=1) :
    0 < -(fderiv ℝ (movingFixedJoinMiddle a h) (1,(b,p)) (1,0) v v) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  have hx : x∈(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).baseSet := by
    change x∈(chartAt (Model n) a).source
    simpa only [x,extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  have hv0 : v≠0 := by intro h; simp only [h,norm_zero] at hv; norm_num at hv
  have hLv : L v≠0 := by
    intro Hz
    have H := congrArg ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x) Hz
    have HL := Trivialization.continuousLinearMapAt_symmL (R := ℝ)
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a) hx v
    exact hv0 (by simpa only [L,HL,map_zero] using H)
  have hLVpos : 0 < ‖L v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hLv)
  have hM := movingFixedJoinMiddle_contDiffAt
    (movingFixedJoinAction_contDiffAt hb hh1.ne' hleft hright)
  have hD := bilinear_time_hasDerivAt (hM.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) v
  obtain ⟨c,hc,HC⟩ := exists_fixedJoinMiddle_lower_crossing hh hh1 hleft hright
  apply derivative_neg_of_lower_crossing hD hh1 (mul_pos hc hLVpos)
  filter_upwards [HC] with T hT
  intro hhT hT1
  have HB1 := (fixedJoinAction_contDiffAt hh1.ne' hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HBT := (fixedJoinAction_shortened_contDiffAt hh1 hhT hT1 hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [movingFixedJoinMiddle_eq hb h T p v v HBT,movingFixedJoinMiddle_eq hb h 1 p v v HB1]
  have H := hT hhT hT1 (L v)
  nlinarith only [H]

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.movingFixedJoinMiddle_strict_crossing_oai.{u_1} := @OAI.WeakMTWTransport.movingFixedJoinMiddle_strict_crossing_oai.{u_1}
