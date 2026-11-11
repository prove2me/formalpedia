-- Prove2me | solution 1 for OAI.WeakMTWTransport.mixed_intrinsic_det
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:27:00.673955+00:00
-- url     : https://prove2.me/submissions/e212071e-f3df-4c3d-8ab1-b6b8558af1da

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactStationarity
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

lemma chartCostCovector_contDiffAt {a b : M} {q : Model n×Model n}
    (ha : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hb : q.2∈(extChartAt 𝓘(ℝ,Model n) b).target)
    (hc : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => cost z.1 z.2)
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1,(extChartAt 𝓘(ℝ,Model n) b).symm q.2)) :
    ContDiffAt ℝ ∞ (chartCostCovector a b) q := by
  let F : Model n → Model n → ℝ := fun y x =>
    chartCost a ((extChartAt 𝓘(ℝ,Model n) b).symm y) x
  have hiA := (contMDiffOn_extChartAt_symm (n := ∞) a).contMDiffAt
    ((isOpen_extChartAt_target a).mem_nhds ha)
  have hiB := (contMDiffOn_extChartAt_symm (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target b).mem_nhds hb)
  have hF : ContDiffAt ℝ ∞ (Function.uncurry F) q.swap :=
    (hc.comp q.swap ((hiA.comp q.swap contDiffAt_snd.contMDiffAt).prodMk
      (hiB.comp q.swap contDiffAt_fst.contMDiffAt))).contDiffAt
  exact (ContDiffAt.partial_snd_fderiv hF).comp q (contDiffAt_snd.prodMk contDiffAt_fst)

end ContactStationarity
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MatrixNormDetFactorial
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Module Set
open scoped BigOperators

namespace WeakMTWTransport

lemma normDet_comp_three {U V W Z : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
    (R : U →L[ℝ] V) (A : V →L[ℝ] W) (S : W →L[ℝ] Z)
    (hUV : finrank ℝ U=finrank ℝ V) (hVW : finrank ℝ V=finrank ℝ W) :
    (S.comp (A.comp R)).toLinearMap.normDet=
      S.toLinearMap.normDet*A.toLinearMap.normDet*R.toLinearMap.normDet := by
  change (S.toLinearMap ∘ₗ (A.toLinearMap ∘ₗ R.toLinearMap)).normDet=_
  rw [LinearMap.normDet_comp_of_finrank_eq _ _ (hUV.trans hVW),
    LinearMap.normDet_comp_of_finrank_eq _ _ hUV,mul_assoc]

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_NormDetAdjoint
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace WeakMTWTransport
lemma normDet_adjoint_of_pos {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [CompleteSpace E] [CompleteSpace F]
    (T:E →L[ℝ] F) (hd:Module.finrank ℝ E=Module.finrank ℝ F)
    (hT:0 < T.toLinearMap.normDet) :
    T.adjoint.toLinearMap.normDet=T.toLinearMap.normDet := by
  have hm:=LinearMap.normDet_comp_of_finrank_eq T.toLinearMap T.adjoint.toLinearMap hd
  have hs:(T.adjoint.comp T).det=T.toLinearMap.normDet^2:=by
    simpa only [RCLike.ofReal_real_eq_id,id_eq] using T.normDet_sq.symm
  rw [LinearMap.normDet_eq_abs_det] at hm
  change |(T.adjoint.comp T).det|=T.adjoint.toLinearMap.normDet*T.toLinearMap.normDet at hm
  rw [hs,abs_of_nonneg (sq_nonneg _),pow_two] at hm
  exact (mul_right_cancel₀ hT.ne' hm).symm
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MixedIntrinsic
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
section MixedIntrinsic
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.finiteMixed
omit [Nonempty M] in
lemma chart_normal_smooth {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    (hp:riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    ContDiffAt ℝ ∞ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp x) p := by
  apply ContMDiffAt.contDiffAt
  apply ContMDiffAt.comp p _ (contMDiff_riemannianExp_fiber x p)
  exact contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hp)

omit [Nonempty M] in
lemma mixed_intrinsic_factor {x a b:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hp:p∈injectivityDomain x)
    (hy:riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    let T := fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp x) 0
    let S := fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) b) ∘ riemannianExp x) p
    T.adjoint.comp ((mixedCostOperator a b (extChartAt 𝓘(ℝ,Model n) a x)
      (extChartAt 𝓘(ℝ,Model n) b (riemannianExp x p))).comp S)=
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ,Model n) x) := by
  dsimp only
  let E:=TangentSpace 𝓘(ℝ,Model n) x
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  let ψ:=extChartAt 𝓘(ℝ,Model n) b
  let f:=χ ∘ riemannianExp (n:=n) x
  let g:=ψ ∘ riemannianExp (n:=n) x
  let T:=fderiv ℝ f 0
  let S:=fderiv ℝ g p
  let G:=chartCostCovector (n:=n) a b
  have hf:ContDiffAt ℝ ∞ f 0:=chart_normal_smooth (by simpa only [riemannianExp_zero] using hx)
  have hg:ContDiffAt ℝ ∞ g p:=chart_normal_smooth hy
  have hf0:f 0=χ x:=by simp only [f,Function.comp_apply,riemannianExp_zero]
  have hgc:ContDiffAt ℝ ∞ G (χ x,g p):=chartCostCovector_contDiffAt
    (χ.map_source hx) (ψ.map_source hy) (by
      change ContMDiffAt _ _ ∞ (fun q:M×M=>cost q.1 q.2) (χ.symm (χ x),ψ.symm (ψ (riemannianExp x p)))
      rw [χ.left_inv hx,ψ.left_inv hy]
      exact cost_contMDiffAt_of_injectivityDomain (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M) hp)
  have hn:∀ᶠ v:E in 𝓝 p,v∈injectivityDomain x ∧ riemannianExp x v∈ψ.source:=by
    filter_upwards [(isOpen_injectivityDomain x).mem_nhds hp,
      (contMDiff_riemannianExp_fiber x p).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source b).mem_nhds hy)] with v hv hw
    exact ⟨hv,hw⟩
  have hsource:∀ᶠ h:E in 𝓝 0,riemannianExp x h∈χ.source:=
    (contMDiff_riemannianExp_fiber x 0).continuousAt.preimage_mem_nhds
      (by simpa only [riemannianExp_zero] using (isOpen_extChartAt_source a).mem_nhds hx)
  have he: (fun v:E => (G (χ x,g v)).comp T) =ᶠ[𝓝 p] (fun v:E => -(innerSL ℝ v)):=by
    filter_upwards [hn] with v hv
    have hcost:ContDiffAt ℝ ∞ (chartCost a (riemannianExp x v)) (χ x):=by
      have H:=cost_contMDiffAt_of_injectivityDomain
        (⟨x,v⟩:TangentBundle 𝓘(ℝ,Model n) M) hv.1
      have hi:ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ χ.symm (χ x):=
        (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds (χ.map_source hx))
      have H':ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
          (fun q:M×M=>cost q.1 q.2) (χ.symm (χ x),riemannianExp x v):=by
        simpa only [χ.left_inv hx] using H
      exact (H'.comp (χ x) (hi.prodMk contMDiffAt_const)).contDiffAt
    have heq:(normalCost x v)=ᶠ[𝓝 (0:E)] ((chartCost a (riemannianExp x v)) ∘ f):=by
      filter_upwards [hsource] with h hh
      change cost (riemannianExp x h) (riemannianExp x v)=cost (χ.symm (χ (riemannianExp x h))) (riemannianExp x v)
      rw [χ.left_inv hh]
    have HD:HasFDerivAt ((chartCost a (riemannianExp x v)) ∘ f)
        ((fderiv ℝ (chartCost a (riemannianExp x v)) (χ x)).comp T) 0:=by
      apply HasFDerivAt.comp 0 _ (hf.differentiableAt (by simp)).hasFDerivAt
      simpa only [hf0] using (hcost.differentiableAt (by simp)).hasFDerivAt
    have HH: (fderiv ℝ (chartCost a (riemannianExp x v)) (χ x)).comp T= -(innerSL ℝ v):=by
      rw [←HD.fderiv,←heq.fderiv_eq,(normalCost_hasFDerivAt_zero hv.1).fderiv]
      simp only [map_neg]
    change (fderiv ℝ (chartCost a (ψ.symm (ψ (riemannianExp x v)))) (χ x)).comp T=_
    rw [ψ.left_inv hv.2]
    exact HH
  have hmap:HasFDerivAt (fun v:E => (χ x,g v))
      ((0:E →L[ℝ] Model n).prod S) p:=
    (hasFDerivAt_const (χ x) p).prodMk (hg.differentiableAt (by simp)).hasFDerivAt
  have hd:=((hgc.differentiableAt (by simp)).hasFDerivAt.comp p hmap).clm_comp
    (hasFDerivAt_const T p)
  have hr:HasFDerivAt (fun v:E => -(innerSL ℝ v)) (-(innerSL ℝ)) p:=
    (innerSL ℝ).hasFDerivAt.neg
  have hde:= (hd.congr_of_eventuallyEq he.symm).unique hr
  apply ContinuousLinearMap.ext
  intro d
  apply ext_inner_right ℝ
  intro e
  have H:=congrArg (fun A:E →L[ℝ] E →L[ℝ] ℝ=>A d e) hde
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.flip_apply,add_apply,zero_apply,zero_add,
    map_zero,neg_apply] at H
  change (fderiv ℝ G (χ x,g p)) (0,S d) (T e) = -inner ℝ d e at H
  change inner ℝ (T.adjoint ((mixedCostOperator a b (χ x) (g p)) (S d))) e=inner ℝ d e
  rw [ContinuousLinearMap.adjoint_inner_left,mixedCostOperator,bilinearOperator_inner]
  simpa only [mixedCostOperator,neg_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply,neg_eq_iff_eq_neg,G,innerSL_apply_apply] using H

end MixedIntrinsic
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_ExponentialJacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
section ExponentialJacobian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteExponentialJacobian (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma expJacobian_zero (x : M) : expJacobian (n := n) x 0=1 := by
  let F : TangentSpace 𝓘(ℝ,Model n) x →ₗ[ℝ] TangentSpace 𝓘(ℝ,Model n) (riemannianExp (n := n) x 0) := (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) 0).toLinearMap
  let e : TangentSpace 𝓘(ℝ,Model n) x →ₗᵢ[ℝ]
      TangentSpace 𝓘(ℝ,Model n) (riemannianExp (n := n) x 0) :=
    { toLinearMap := F, norm_map' := mfderiv_exp_zero_norm x }
  exact e.normDet_eq_one

end ExponentialJacobian
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_IntrinsicJacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
section IntrinsicJacobian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.tangentFiniteIntrinsicJacobian
omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartJacobian_nonneg (a x : M) : 0 ≤ chartJacobian (n := n) a x :=
  LinearMap.normDet_nonneg _

lemma normDet_chart_exp (a x : M) (p : TangentSpace 𝓘(ℝ,Model n) x)
    (hp : riemannianExp (n := n) x p∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) p).toLinearMap.normDet=
      chartJacobian (n := n) a (riemannianExp (n := n) x p)*expJacobian (n := n) x p := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let E : V →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) :=
    mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) p
  let C : TangentSpace 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) →L[ℝ] Model n :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) (extChartAt 𝓘(ℝ,Model n) a) (riemannianExp (n := n) x p)
  have hd := mfderiv_comp p (mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hp))
    ((contMDiff_riemannianExp_fiber x p).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  change fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) p=C.comp E at hd
  rw [hd]
  exact LinearMap.normDet_comp_of_finrank_eq E.toLinearMap C.toLinearMap rfl

lemma normDet_chart_exp_zero (a x : M)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) 0).toLinearMap.normDet=
      chartJacobian (n := n) a x := by
  have h := normDet_chart_exp a x 0 (by simpa only [riemannianExp_zero] using hx)
  rw [expJacobian_zero,mul_one] at h
  simpa only [riemannianExp_zero] using h

end IntrinsicJacobian
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_ChartJacobianBounds
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
section ChartJacobianBounds
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteChartJacobianBounds (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance inverseChartNormedAddCommGroup_r0a33f3_1 (y : Model n) (x : M) : NormedAddCommGroup
    (TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance inverseChartNormedSpace_r0a33f3_1 (y : Model n) (x : M) : NormedSpace ℝ
    (TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x) :=
  ContinuousLinearMap.toNormedSpace
omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartJacobian_inverse_product (a : M) {z : Model n}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    chartJacobian (n := n) a ((extChartAt 𝓘(ℝ,Model n) a).symm z)*
      inverseChartJacobian (n := n) a z=1 := by
  let d := extChartAt 𝓘(ℝ,Model n) a
  let F : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (d.symm z) :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d.symm z
  let G : TangentSpace 𝓘(ℝ,Model n) (d.symm z) →L[ℝ] Model n :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d (d.symm z)
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hz
  simp only [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at h
  change G.comp F=ContinuousLinearMap.id ℝ (Model n) at h
  have hn := congrArg (fun L : Model n →L[ℝ] Model n => L.toLinearMap.normDet) h
  change (G.toLinearMap ∘ₗ F.toLinearMap).normDet=(LinearMap.id : Model n →ₗ[ℝ] Model n).normDet at hn
  rw [LinearMap.normDet_comp_of_finrank_eq F.toLinearMap G.toLinearMap rfl,LinearMap.normDet_id] at hn
  exact hn

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartJacobian_pos {a x : M} (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    0 < chartJacobian (n := n) a x := by
  have h := chartJacobian_inverse_product a ((extChartAt 𝓘(ℝ,Model n) a).map_source hx)
  rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv hx] at h
  apply (chartJacobian_nonneg a x).lt_of_ne'
  intro he
  rw [he,zero_mul] at h
  exact zero_ne_one h

end ChartJacobianBounds
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MixedDetIntrinsic
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
section MixedDetIntrinsic
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance midFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [Nonempty M] in
lemma mixed_intrinsic_det_oai {x a b:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hp:p∈injectivityDomain x)
    (hy:riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    chartJacobian (n:=n) a x *
      |(mixedCostOperator a b (extChartAt 𝓘(ℝ,Model n) a x)
        (extChartAt 𝓘(ℝ,Model n) b (riemannianExp x p))).det| *
      (chartJacobian (n:=n) b (riemannianExp x p)*expJacobian (n:=n) x p)=1 := by
  let E:=TangentSpace 𝓘(ℝ,Model n) x
  let T:=fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n:=n) x) 0
  let S:=fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) b) ∘ riemannianExp (n:=n) x) p
  let B:=mixedCostOperator a b (extChartAt 𝓘(ℝ,Model n) a x)
    (extChartAt 𝓘(ℝ,Model n) b (riemannianExp x p))
  have hT:T.toLinearMap.normDet=chartJacobian (n:=n) a x:=normDet_chart_exp_zero _ _ hx
  have hS:S.toLinearMap.normDet=chartJacobian (n:=n) b (riemannianExp x p)*expJacobian (n:=n) x p:=
    normDet_chart_exp _ _ _ hy
  have hTa:T.adjoint.toLinearMap.normDet=T.toLinearMap.normDet:=
    normDet_adjoint_of_pos T rfl (hT.symm ▸ chartJacobian_pos hx)
  have H:=congrArg (fun A:E →L[ℝ] E=>A.toLinearMap.normDet) (mixed_intrinsic_factor hx hp hy)
  change (T.adjoint.comp (B.comp S)).toLinearMap.normDet=(LinearMap.id:E →ₗ[ℝ] E).normDet at H
  rw [normDet_comp_three S B T.adjoint rfl rfl,LinearMap.normDet_id,hTa,hT,hS,
    LinearMap.normDet_eq_abs_det] at H
  exact H

end MixedDetIntrinsic
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.mixed_intrinsic_det_oai.{u_1} := @OAI.WeakMTWTransport.mixed_intrinsic_det_oai.{u_1}
