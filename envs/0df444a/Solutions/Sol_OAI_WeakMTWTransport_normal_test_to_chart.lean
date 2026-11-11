-- Prove2me | solution 1 for OAI.WeakMTWTransport.normal_test_to_chart
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:27:01.925539+00:00
-- url     : https://prove2.me/submissions/e2106002-a88a-483f-8593-0f36f71fb5ab

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartGradientMap
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
lemma chartGradientVector_total_eq {a : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm q.1,chartGradientVector a q.1 q.2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) =
      (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)).symm
        (q.1,(riemannianCoordinateMetric a q.1).inverse q.2) := by
  have hx : (extChartAt 𝓘(ℝ,Model n) a).symm q.1∈(chartAt (Model n) a).source := by
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hq
  dsimp only [chartGradientVector]
  rw [TangentBundle.symmL_trivializationAt_eq_core hx]
  rfl

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

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_chart_fiber_log {x a : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x)
    (ha : riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let ψ := extChartAt 𝓘(ℝ,Model n) a
    let u := ψ (riemannianExp x p)
    ∃ e : Model n → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ e u ∧ e u=p ∧
      (∀ᶠ w in 𝓝 u, riemannianExp x (e w)=ψ.symm w) ∧
      Function.Injective (fderiv ℝ e u) := by
  let ψ := extChartAt 𝓘(ℝ,Model n) a
  let u := ψ (riemannianExp x p)
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hu : u∈ψ.target := ψ.map_source ha
  have hui : ψ.symm u=riemannianExp x p := ψ.left_inv ha
  obtain ⟨L,hL,hLp,hLi⟩ := exists_smooth_fiber_log hp
  have hi : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ ψ.symm u :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hu)
  let e := fun w : Model n => L (ψ.symm w)
  have he : ContDiffAt ℝ ∞ e u :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L (ψ.symm u) from by
      simpa only [hui] using hL).comp u hi).contDiffAt
  have heu : e u=p := by dsimp [e]; rw [hui]; exact hLp
  have hei : ∀ᶠ w in 𝓝 u, riemannianExp x (e w)=ψ.symm w :=
    hi.continuousAt.eventually (by simpa only [hui] using hLi)
  refine ⟨e,he,heu,hei,?_⟩
  let c : V → Model n := fun v => ψ (riemannianExp x v)
  have hc : ContDiffAt ℝ ∞ c p :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ,Model n)) (by
      simpa only [extChartAt_source] using ha)).comp p
        (contMDiff_riemannianExp_fiber x p)).contDiffAt
  have hid : (fun w => c (e w)) =ᶠ[𝓝 u] (fun w => w) := by
    filter_upwards [hei,(isOpen_extChartAt_target a).mem_nhds hu] with w hw hwt
    dsimp [c]
    rw [hw,ψ.right_inv hwt]
  have HD := hid.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp u (by simpa only [heu] using hc.differentiableAt (by simp))
    (he.differentiableAt (by simp)),fderiv_fun_id] at HD
  intro v w hvw
  change fderiv ℝ e u v=fderiv ℝ e u w at hvw
  have H := congrArg (fun C : Model n →L[ℝ] Model n => C v-C w) HD
  apply sub_eq_zero.mp
  simpa only [ContinuousLinearMap.comp_apply,hvw,sub_self,ContinuousLinearMap.id_apply] using H.symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_SecondFderivAdd
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

lemma second_fderiv_add_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    fderiv ℝ (fderiv ℝ (fun w => f w+g w)) z =
      fderiv ℝ (fderiv ℝ f) z+fderiv ℝ (fderiv ℝ g) z := by
  have he : fderiv ℝ (fun w => f w+g w) =ᶠ[𝓝 z]
      (fun w => fderiv ℝ f w+fderiv ℝ g w) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with w hw hw'
    exact fderiv_fun_add (hw.differentiableAt (by norm_num)) (hw'.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  exact fderiv_fun_add ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MixedIntrinsic
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

end MixedIntrinsic
end WeakMTWTransport

end
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_NormLower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

end WeakMTWTransport

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalTestChart
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
section NormalTestChart
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.normalTestFinite
omit [Nonempty M] in
lemma exists_chart_covector_for_log_fixed {a x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hp : p∈injectivityDomain x) :
    let z := extChartAt 𝓘(ℝ,Model n) a x
    ∃ L : Model n →L[ℝ] ℝ,
      chartGradientVector a z L∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
      coordinateBackward a (-1,z,L)=riemannianExp x p ∧
      HasFDerivAt (chartCost a (riemannianExp x p)) (-L) z := by
  let : Nonempty M := ⟨a⟩
  let z := extChartAt 𝓘(ℝ,Model n) a x
  let A : TangentBundle 𝓘(ℝ,Model n) M := ⟨a,0⟩
  let P : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let c := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) A
  let L := riemannianCoordinateMetric a z (c P).2
  have hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source hx
  have hPs : P∈c.source := (tangent_chart_source_iff A P).mpr hx
  have he : (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,chartGradientVector a z L⟩ :
      TangentBundle 𝓘(ℝ,Model n) M)=P := by
    rw [chartGradientVector_total_eq (q := (z,L)) hz]
    have hinv : (riemannianCoordinateMetric a z).inverse L=(c P).2 :=
      (riemannianCoordinateMetric_isInvertible hz).inverse_apply_self _
    rw [hinv]
    exact c.left_inv hPs
  have hreg : chartGradientVector a z L∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z) := by
    have H : P∈{Q : TangentBundle 𝓘(ℝ,Model n) M | Q.2∈injectivityDomain Q.1} := hp
    rwa [←he] at H
  have hex : coordinateBackward a (-1,z,L)=riemannianExp x p := by
    rw [coordinateBackward_eq_exp_chartGradient hz]
    exact congrArg (fun Q : TangentBundle 𝓘(ℝ,Model n) M => riemannianExp Q.1 Q.2) he
  refine ⟨L,hreg,hex,?_⟩
  rw [←hex]
  exact chartCost_gradient_at_contact hz hreg

omit [Nonempty M] in
lemma normal_test_to_chart_oai {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source) (hp:p∈injectivityDomain x)
    {u:M → ℝ} {φ:TangentSpace 𝓘(ℝ,Model n) x → ℝ}
    (hφ:ContDiffAt ℝ 2 φ 0) (hφD:fderiv ℝ φ 0=innerSL ℝ p)
    (hval:u x=φ 0) (hlo:∀ᶠ w in 𝓝 0,φ w≤u (riemannianExp x w))
    (hpos:∃m>0,∀d,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue x p d) :
    let z:=extChartAt 𝓘(ℝ,Model n) a x
    ∃ψ:Model n → ℝ,∃R:Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ 2 ψ z ∧
      chartGradientVector a z (fderiv ℝ ψ z)∈injectivityDomain
        ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
      coordinateBackward a (-1,z,fderiv ℝ ψ z)=riemannianExp x p ∧
      u ((extChartAt 𝓘(ℝ,Model n) a).symm z)=ψ z ∧
      (∀ᶠ w in 𝓝 z,ψ w≤u ((extChartAt 𝓘(ℝ,Model n) a).symm w)) ∧
      (∃k>0,∀d:Model n,k*‖d‖^2≤fderiv ℝ (fderiv ℝ ψ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp x p))) z d d) ∧
      chartJacobian (n:=n) a x*R.toLinearMap.normDet=1 ∧
      bilinearOperator (fderiv ℝ (fderiv ℝ ψ) z+
        fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp x p))) z)=
        R.adjoint.comp ((bilinearOperator
          (fderiv ℝ (fderiv ℝ φ) 0+normalHessian x p)).comp R) := by
  let z:=extChartAt 𝓘(ℝ,Model n) a x
  let E:=TangentSpace 𝓘(ℝ,Model n) x
  let c:=normalCost x p
  obtain ⟨m,hm,hpos⟩:=hpos
  obtain ⟨L,hLreg,hLb,hLD⟩:=exists_chart_covector_for_log_fixed hx hp
  obtain ⟨e,he,he0,hei,hi⟩:=exists_smooth_chart_fiber_log (a:=a)
    (zero_mem_injectivityDomain (n:=n) x) (by simpa only [riemannianExp_zero] using hx)
  simp only [riemannianExp_zero] at he he0 hei hi
  change ContDiffAt ℝ ∞ e z at he
  change e z=0 at he0
  change Function.Injective (fderiv ℝ e z) at hi
  have he2:ContDiffAt ℝ 2 e z:=he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨k,hk,Hk⟩:=exists_norm_sq_lower_of_injective (fderiv ℝ e z) hi
  let ψ:Model n → ℝ:=fun w=>φ (e w)
  let R:=fderiv ℝ e z
  have hψ:ContDiffAt ℝ 2 ψ z:=(he0.symm ▸ hφ).comp z he2
  have hc:ContDiffAt ℝ 2 c 0:=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hce:chartCost a (riemannianExp x p)=ᶠ[𝓝 z] (fun w=>c (e w)):=by
    filter_upwards [hei] with w hw
    simp only [c,normalCost,chartCost,hw]
  have hcc:ContDiffAt ℝ 2 (chartCost a (riemannianExp x p)) z:=
    ((he0.symm ▸ hc).comp z he2).congr_of_eventuallyEq hce
  have hψD:fderiv ℝ ψ z=L:=by
    have Hc:=hce.fderiv_eq (𝕜:=ℝ)
    rw [hLD.fderiv,fderiv_fun_comp z
      (by simpa only [he0] using hc.differentiableAt (by norm_num))
      (he2.differentiableAt (by norm_num)),he0,(normalCost_hasFDerivAt_zero hp).fderiv] at Hc
    rw [show ψ=(fun w=>φ (e w)) from rfl,fderiv_fun_comp z
      (by simpa only [he0] using hφ.differentiableAt (by norm_num))
      (he2.differentiableAt (by norm_num)),he0,hφD]
    apply ContinuousLinearMap.ext
    intro d
    have HH:=congrArg (fun A:Model n →L[ℝ] ℝ=>A d) Hc
    simpa only [neg_apply,ContinuousLinearMap.comp_apply,
      innerSL_apply_apply,inner_neg_left,neg_inj] using HH.symm
  have hψlo:∀ᶠ w in 𝓝 z,ψ w≤u ((extChartAt 𝓘(ℝ,Model n) a).symm w):=by
    have HH:=he.continuousAt.eventually
      (show ∀ᶠ v in 𝓝 (e z),φ v≤u (riemannianExp x v) by rwa [he0])
    filter_upwards [HH,hei] with w hw hwi
    simpa only [ψ,hwi] using hw
  have Hpull (d v:Model n): fderiv ℝ (fderiv ℝ ψ) z d v+
      fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp x p))) z d v=
      fderiv ℝ (fderiv ℝ φ) 0 (R d) (R v)+normalHessian x p (R d) (R v):=by
    have hzF:fderiv ℝ (fun v=>φ v+c v) 0=0:=by
      rw [fderiv_fun_add (hφ.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)),
        hφD,(normalCost_hasFDerivAt_zero hp).fderiv]
      simp only [map_neg,add_neg_cancel]
    have HF:=second_fderiv_comp_stationary (f:=fun v=>φ v+c v) (g:=e)
      (he0.symm ▸ hφ.add hc) he2 (by rwa [he0]) d v
    rw [he0,second_fderiv_add_eq hφ hc] at HF
    have Heq:(fun w=>ψ w+chartCost a (riemannianExp x p) w)=ᶠ[𝓝 z]
        (fun w=>φ (e w)+c (e w)):=by
      filter_upwards [hce] with w hw
      rw [hw]
    have HH:=congrArg (fun A:Model n →L[ℝ] Model n →L[ℝ] ℝ=>A d v) Heq.fderiv.fderiv_eq
    rw [second_fderiv_add_eq hψ hcc] at HH
    exact HH.trans HF
  have hRp: (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n:=n) x) 0).comp R=
      ContinuousLinearMap.id ℝ (Model n):=by
    let f: E → Model n := (extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n:=n) x
    have hf:ContDiffAt ℝ ∞ f 0:=chart_normal_smooth (by simpa only [riemannianExp_zero] using hx)
    have hid:(fun w=>f (e w))=ᶠ[𝓝 z] (fun w=>w):=by
      filter_upwards [hei,(isOpen_extChartAt_target a).mem_nhds
        ((extChartAt 𝓘(ℝ,Model n) a).map_source hx)] with w hw ht
      simp only [f,Function.comp_apply,hw,(extChartAt 𝓘(ℝ,Model n) a).right_inv ht]
    have HD:=hid.fderiv_eq (𝕜:=ℝ)
    rw [fderiv_fun_comp z (by simpa only [he0] using hf.differentiableAt (by simp))
      (he.differentiableAt (by simp)),he0,fderiv_fun_id] at HD
    exact HD
  have hRdet:chartJacobian (n:=n) a x*R.toLinearMap.normDet=1:=by
    have hh:=congrArg (fun F:Model n →L[ℝ] Model n=>F.toLinearMap.normDet) hRp
    rw [show (ContinuousLinearMap.id ℝ (Model n)).toLinearMap=LinearMap.id by rfl,
      LinearMap.normDet_id] at hh
    change ((fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n:=n) x) 0).toLinearMap ∘ₗ
      R.toLinearMap).normDet=1 at hh
    erw [LinearMap.normDet_comp_of_finrank_eq R.toLinearMap
      (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n:=n) x) 0).toLinearMap rfl] at hh
    rwa [normDet_chart_exp_zero a x hx] at hh
  refine ⟨ψ,R,hψ,?_,?_,?_,hψlo,?_,hRdet,?_⟩
  · rwa [hψD]
  · rwa [hψD]
  · change u ((extChartAt 𝓘(ℝ,Model n) a).symm z)=φ (e z)
    rw [he0]
    exact ((congrArg u ((extChartAt 𝓘(ℝ,Model n) a).left_inv hx)).trans hval)
  · refine ⟨m*k,mul_pos hm hk,fun d=>?_⟩
    rw [Hpull]
    simp only [hessianValue_eq_normalHessian hp] at hpos
    calc
      _ = m*(k*‖d‖^2):=by ring
      _ ≤ m*‖R d‖^2:=mul_le_mul_of_nonneg_left (Hk d) hm.le
      _ ≤ _:=hpos (R d)
  · apply ContinuousLinearMap.ext
    intro d
    apply ext_inner_right ℝ
    intro v
    simp only [bilinearOperator_inner,add_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
    exact Hpull d v

end NormalTestChart
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.normal_test_to_chart_oai.{u_1} := @OAI.WeakMTWTransport.normal_test_to_chart_oai.{u_1}
