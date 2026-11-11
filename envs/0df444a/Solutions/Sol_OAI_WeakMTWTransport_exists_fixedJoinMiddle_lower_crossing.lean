-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_fixedJoinMiddle_lower_crossing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:48.750778+00:00
-- url     : https://prove2.me/submissions/e367c5f3-5991-492f-8c03-607edd3c5a71

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
import Theorems.Thm_OAI_WeakMTWTransport_exists_uniform_divided_hessian_gap

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FiberLog
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_fiber_log {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) :
    ∃ L : M → TangentSpace 𝓘(ℝ,Model n) x,
      ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) ∞ L
        (riemannianExp x p) ∧
      L (riemannianExp x p)=p ∧
      (∀ᶠ y in 𝓝 (riemannianExp x p), riemannianExp x (L y)=y) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  let d := extChartAt 𝓘(ℝ,Model n) y
  obtain ⟨e,he,hpe,hei⟩ := exists_coordinate_exp_inverse hp
  have hep : e p=d y := by rw [he]
  let L : M → V := fun z => e.symm (d z)
  have hL : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L y :=
    (show ContDiffAt ℝ ∞ e.symm (d y) from hep ▸ hei).contMDiffAt.comp y
      (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y from contMDiffAt_extChartAt)
  have hLy : L y=p := by dsimp [L]; rw [←hep,e.left_inv hpe]
  refine ⟨L,hL,hLy,?_⟩
  have ht : ∀ᶠ z in 𝓝 y, d z∈e.target :=
    (continuousAt_extChartAt y).eventually
      ((e.open_target.mem_nhds (hep ▸ e.map_source hpe)))
  have hcont : ContinuousAt (fun z => riemannianExp x (L z)) y :=
    (continuous_riemannianExp x).continuousAt.comp hL.continuousAt
  have hs : ∀ᶠ z in 𝓝 y, riemannianExp x (L z)∈d.source := by
    have H := hcont.eventually (show d.source∈𝓝 (riemannianExp x (L y)) from by
      rw [hLy]; exact extChartAt_source_mem_nhds y)
    exact H
  filter_upwards [ht,hs,extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) y] with z hzt hzs hsz
  apply d.injOn hzs hsz
  have HR := e.right_inv hzt
  rw [he] at HR
  exact HR

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_StationaryPullback
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

lemma second_fderiv_sub {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f a-g a)) x v w =
      fderiv ℝ (fderiv ℝ f) x v w-fderiv ℝ (fderiv ℝ g) x v w := by
  have he : fderiv ℝ (fun a => f a-g a) =ᶠ[𝓝 x]
      (fun a => fderiv ℝ f a-fderiv ℝ g a) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with a ha hb
    exact fderiv_fun_sub (ha.differentiableAt (by norm_num)) (hb.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  rw [fderiv_fun_sub ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]
  rfl

lemma second_fderiv_const_mul {f : E → ℝ} {x : E} (c : ℝ) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => c*f a)) x v w = c*fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fderiv ℝ (c • f)) x v w = _
  rw [fderiv_const_smul_field c]
  rw [fderiv_const_smul_field (f := fderiv ℝ f) c]
  rfl

lemma second_fderiv_comp_stationary {f : F → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x)
    (hzero : fderiv ℝ f (g x)=0) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f (g a))) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := g) x hgd
  have hd2 := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hd := hd1.clm_comp hd2
  have heq : (fun a => (fderiv ℝ f (g a)).comp (fderiv ℝ g a)) =ᶠ[𝓝 x]
      fderiv ℝ (fun a => f (g a)) := by
    filter_upwards [hgd.continuousAt.eventually (hf.eventually (by norm_num)),
      hg.eventually (by norm_num)] with a hfa hga
    exact ((hfa.differentiableAt (by norm_num)).hasFDerivAt.comp (f := g) a
      (hga.differentiableAt (by norm_num)).hasFDerivAt).fderiv.symm
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w)
    (hd.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [Function.comp_apply,hzero,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_comp,zero_apply,
    zero_add,add_zero,add_apply] using H

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_DividedPullback
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma divided_cost_difference_pullback {z : M} {p : TangentSpace 𝓘(ℝ,Model n) z}
    {t : ℝ} {g : E → TangentSpace 𝓘(ℝ,Model n) z} {a : E}
    (hp : p∈injectivityDomain z) (htp : t • p∈injectivityDomain z) (ht : t≠0)
    (hg : ContDiffAt ℝ 2 g a) (hg0 : g a=0) (k : E) :
    fderiv ℝ (fderiv ℝ (fun b =>
      normalCost z (t • p) (g b)/t-normalCost z p (g b))) a k k =
    hessianValue z (t • p) (fderiv ℝ g a k)/t-
      hessianValue z p (fderiv ℝ g a k) := by
  let F := fun v => t⁻¹*normalCost z (t • p) v-normalCost z p v
  have hA := (normalCost_contDiffAt htp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hB := (normalCost_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hF : ContDiffAt ℝ 2 F 0 := (contDiffAt_const.mul hA).sub hB
  have hzero : fderiv ℝ F 0=0 := by
    ext v
    rw [fderiv_fun_sub ((hA.differentiableAt (by norm_num)).const_mul _)
      (hB.differentiableAt (by norm_num))]
    change (fderiv ℝ (t⁻¹ • normalCost z (t • p)) 0) v-
      fderiv ℝ (normalCost z p) 0 v=0
    rw [fderiv_const_smul_field]
    simp only [Pi.smul_apply,smul_apply,smul_eq_mul,
      normalCost_fderiv_zero htp,normalCost_fderiv_zero hp,real_inner_smul_left]
    field_simp [ht]
    ring
  have HH := second_fderiv_comp_stationary (g := g)
    (by simpa only [hg0] using hF) hg (by simpa only [hg0] using hzero) k k
  rw [hg0,second_fderiv_sub (contDiffAt_const.mul hA) hB,
    second_fderiv_const_mul] at HH
  rw [hessianValue_eq_normalHessian htp,hessianValue_eq_normalHessian hp]
  simpa only [F,normalHessian,div_eq_mul_inv,mul_comm] using HH
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FixedJoinMiddle
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

section
omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma fixedJoinMiddle_eq_slice {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hB : ContDiffAt ℝ 2 (fixedJoinAction x h T p) (0,p))
    (v w : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h T p v w=fderiv ℝ
      (fderiv ℝ (fun b => fixedJoinAction x h T p (0,b))) p v w := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let I : V →L[ℝ] V×V := (0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)
  have H := second_fderiv_comp_affine (f := fixedJoinAction x h T p) I 0 p
    (by simpa [I] using hB) v w
  simpa [I,fixedJoinMiddle_apply] using H.symm

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FixedJoinDifference
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

lemma fixedJoinMiddle_difference_normal {x z : M} {h T t : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {q : TangentSpace 𝓘(ℝ,Model n) z}
    {g : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) z}
    (ht : t≠0) (htime : T-h=(1-h)*t)
    (hq : q∈injectivityDomain z) (htq : t • q∈injectivityDomain z)
    (hq1 : riemannianExp z q=riemannianExp x p)
    (hqT : riemannianExp z (t • q)=riemannianExp x (T • p))
    (hg : ContDiffAt ℝ 2 g p) (hg0 : g p=0)
    (hgi : ∀ᶠ b in 𝓝 p, riemannianExp z (g b)=riemannianExp x (h • b))
    (hBT : ContDiffAt ℝ 2 (fixedJoinAction x h T p) (0,p))
    (hB1 : ContDiffAt ℝ 2 (fixedJoinAction x h 1 p) (0,p))
    (k : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h T p k k-fixedJoinMiddle x h 1 p k k=
      (hessianValue z (t • q) (fderiv ℝ g p k)/t-
        hessianValue z q (fderiv ℝ g p k))/(1-h) := by
  have hST := hBT.comp p (contDiffAt_const.prodMk contDiffAt_id)
  have hS1 := hB1.comp p (contDiffAt_const.prodMk contDiffAt_id)
  change ContDiffAt ℝ 2 (fun b => fixedJoinAction x h T p (0,b)) p at hST
  change ContDiffAt ℝ 2 (fun b => fixedJoinAction x h 1 p (0,b)) p at hS1
  have he : (fun b => fixedJoinAction x h T p (0,b)-fixedJoinAction x h 1 p (0,b)) =ᶠ[𝓝 p]
      (fun b => (1-h)⁻¹*(normalCost z (t • q) (g b)/t-normalCost z q (g b))) := by
    filter_upwards [hgi] with b hb
    simp only [fixedJoinAction,normalCost,hb,hq1,hqT,one_smul,htime,div_eq_mul_inv,mul_inv_rev]
    ring
  have H := congrArg (fun A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
      TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => A k k) (he.fderiv (𝕜 := ℝ)).fderiv_eq
  rw [second_fderiv_sub hST hS1,second_fderiv_const_mul,
    divided_cost_difference_pullback hq htq ht hg hg0] at H
  rw [fixedJoinMiddle_eq_slice hBT,fixedJoinMiddle_eq_slice hB1]
  simpa only [div_eq_mul_inv,mul_comm] using H

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_JoiningCoordinates
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

lemma exists_smooth_joining_coordinates {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {h : ℝ} (hh : h≠0) (hp : h • p∈injectivityDomain x) :
    let z := riemannianExp x (h • p)
    ∃ g : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) z,
      ContDiffAt ℝ ∞ g p ∧ g p=0 ∧
      (∀ᶠ b in 𝓝 p, riemannianExp z (g b)=riemannianExp x (h • b)) ∧
      Function.Injective (fderiv ℝ g p) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let z := riemannianExp x (h • p)
  let W := TangentSpace 𝓘(ℝ,Model n) z
  obtain ⟨L,hL,hL0,hLi⟩ := exists_smooth_fiber_log (zero_mem_injectivityDomain (n := n) z)
  simp only [riemannianExp_zero] at hL hL0 hLi
  let s : V →L[ℝ] V := h • ContinuousLinearMap.id ℝ V
  have hc : ContMDiffAt 𝓘(ℝ,V) 𝓘(ℝ,Model n) ∞
      (fun b : V => riemannianExp x (h • b)) p :=
    (contMDiff_riemannianExp_fiber x (h • p)).comp p s.contDiff.contMDiff.contMDiffAt
  let g : V → W := fun b => L (riemannianExp x (h • b))
  have hg : ContDiffAt ℝ ∞ g p := (hL.comp p hc).contDiffAt
  have hg0 : g p=0 := hL0
  have hgi : ∀ᶠ b in 𝓝 p, riemannianExp z (g b)=riemannianExp x (h • b) :=
    hc.continuousAt.eventually hLi
  refine ⟨g,hg,hg0,hgi,?_⟩
  let cx : V → Model n := fun v => extChartAt 𝓘(ℝ,Model n) z (riemannianExp x v)
  let cz : W → Model n := fun v => extChartAt 𝓘(ℝ,Model n) z (riemannianExp z v)
  have hcx : ContDiffAt ℝ ∞ cx (h • p) :=
    (contMDiffAt_extChartAt.comp (h • p) (contMDiff_riemannianExp_fiber x (h • p))).contDiffAt
  have hcz : ContDiffAt ℝ ∞ cz 0 := by
    have H := (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞
      (extChartAt 𝓘(ℝ,Model n) z) (riemannianExp z (0:W)) from by
        simpa only [riemannianExp_zero] using
          (contMDiffAt_extChartAt (I := 𝓘(ℝ,Model n)) (x := z))).comp 0
        (contMDiff_riemannianExp_fiber z 0)
    exact H.contDiffAt
  have he : (fun b => cz (g b)) =ᶠ[𝓝 p] (fun b => cx (s b)) :=
    hgi.mono (fun _ hb => congrArg (extChartAt 𝓘(ℝ,Model n) z) hb)
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp p (by simpa only [hg0] using hcz.differentiableAt (by simp))
    (hg.differentiableAt (by simp)),fderiv_fun_comp p (f := s) (g := cx)
    (by simpa [s] using hcx.differentiableAt (by simp)) s.differentiableAt,s.fderiv] at hd
  intro v w hvw
  have H := congrArg (fun A : V →L[ℝ] Model n => A v-A w) hd
  simp only [ContinuousLinearMap.comp_apply,hvw,sub_self] at H
  have hi : Function.Injective (fderiv ℝ cx (h • p)) :=
    riemannianExp_interior_nonconjugate hp
  have Hs : s v=s w := hi (by simpa [s] using sub_eq_zero.mp H.symm)
  apply (smul_right_injective V hh)
  simpa [s] using Hs

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_NormLower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]

lemma exists_norm_sq_lower_of_injective (L : E →L[ℝ] F) (hL : Function.Injective L) :
    ∃ c>0, ∀ v:E, c*‖v‖^2 ≤ ‖L v‖^2 := by
  obtain ⟨K,hK,HK⟩ := L.toLinearMap.injective_iff_antilipschitz.mp hL
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  refine ⟨((K:ℝ)^2)⁻¹,inv_pos.mpr (sq_pos_of_pos hKr),?_⟩
  intro v
  have H := ZeroHomClass.bound_of_antilipschitz L HK v
  have H2 := (sq_le_sq₀ (norm_nonneg v) (mul_nonneg K.coe_nonneg (norm_nonneg (L v)))).mpr H
  rw [mul_pow] at H2
  have HH : ‖v‖^2/(K:ℝ)^2 ≤ ‖L v‖^2 :=
    (div_le_iff₀ (sq_pos_of_pos hKr)).mpr (by simpa only [mul_comm] using H2)
  simpa only [div_eq_mul_inv,mul_comm] using HH

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_fixedJoinMiddle_lower_crossing_oai {x : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hh : 0<h) (hh1 : h<1)
    (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∃ c>0, ∀ᶠ T in 𝓝 (1:ℝ), h<T → T<1 →
      ∀ k : TangentSpace 𝓘(ℝ,Model n) x,
        c*(1-T)*‖k‖^2 ≤ fixedJoinMiddle x h T p k k-fixedJoinMiddle x h 1 p k k := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let : FiniteDimensional ℝ V := inferInstanceAs (FiniteDimensional ℝ (Model n))
  let z := (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
  let q : TangentSpace 𝓘(ℝ,Model n) z :=
    (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2
  have Hcoords := exists_smooth_joining_coordinates hh.ne' hleft
  dsimp only at Hcoords
  rw [riemannianExp_smul] at Hcoords
  obtain ⟨g,hg,hg0,hgi,hginj⟩ := Hcoords
  obtain ⟨a,ha,Ha⟩ := exists_norm_sq_lower_of_injective (fderiv ℝ g p) hginj
  obtain ⟨c,hc,Hc⟩ := exists_uniform_divided_hessian_gap (n := n) (M := M) ‖q‖
  have hden : 0<1-h := sub_pos.mpr hh1
  let t : ℝ → ℝ := fun T => (T-h)/(1-h)
  have htcont : ContinuousAt t 1 := by fun_prop
  have ht1 : t 1=1 := div_self hden.ne'
  have htend : Tendsto t (𝓝 1) (𝓝 1) := by simpa only [ht1] using htcont.tendsto
  refine ⟨c*a/(1-h)^2,div_pos (mul_pos hc ha) (sq_pos_of_pos hden),?_⟩
  filter_upwards [htend.eventually Hc] with T hCT
  intro hT hT1 k
  have ht0 : 0<t T := div_pos (sub_pos.mpr hT) hden
  have htt1 : t T<1 := (div_lt_one hden).mpr (by linarith)
  have htq : t T • q∈injectivityDomain z :=
    contracted_minimizer_mem_injectivityDomain (injectivityDomain_subset_minimizingVectors z hright) ht0 htt1
  have heT : t T • q=(T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 := by
    dsimp [t,q]
    rw [smul_smul,div_mul_cancel₀ _ hden.ne']
  have hBT := (fixedJoinAction_contDiffAt hT.ne' hleft (heT ▸ htq)).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hB1 := (fixedJoinAction_contDiffAt hh1.ne' hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HD := fixedJoinMiddle_difference_normal ht0.ne'
    (by dsimp [t]; field_simp)
    hright htq (shifted_exp_endpoint x p h)
    (by rw [heT]; exact shifted_exp_time x p h T)
    (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hg0 hgi hBT hB1 k
  rw [HD]
  have HH := hCT z q (fderiv ℝ g p k) le_rfl ht0 htt1 hright
  have H : c*(1-t T)*‖fderiv ℝ g p k‖^2 ≤
      hessianValue z (t T • q) (fderiv ℝ g p k)/(t T)-hessianValue z q (fderiv ℝ g p k) := by
    linarith only [HH]
  have HA := mul_le_mul_of_nonneg_left (Ha k) (mul_nonneg hc.le (sub_pos.mpr htt1).le)
  have HL := (div_le_div_iff_of_pos_right hden).mpr (HA.trans H)
  convert! HL using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [t]
  field_simp
  ring

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.exists_fixedJoinMiddle_lower_crossing_oai.{u_1} := @OAI.WeakMTWTransport.exists_fixedJoinMiddle_lower_crossing_oai.{u_1}
