-- Prove2me | solution 1 for OAI.WeakMTWTransport.MaximumDiagonal.good_centers
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:42:18.651205+00:00
-- url     : https://prove2.me/submissions/1117646c-b342-4b88-b7b9-09080e94baff

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
import Definitions.Def_OAIQ232A030

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_EnvelopePole
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma upper_contact_fderiv {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hle : f ≤ᶠ[𝓝 x] g) (heq : f x=g x) : fderiv ℝ f x=fderiv ℝ g x := by
  have hmin : IsLocalMin (g-f) x := by
    filter_upwards [hle] with y hy
    change g x-f x≤g y-f y
    rw [heq,sub_self]
    exact sub_nonneg.mpr hy
  have H := hmin.hasFDerivAt_eq_zero (hg.hasFDerivAt.sub hf.hasFDerivAt)
  exact (sub_eq_zero.mp H).symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_SmoothSupportSemibound
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_comp_with_acceleration {f : F → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f (g a))) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)+
        fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) := by
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
  simpa only [Function.comp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,add_apply,add_comm] using H

lemma bilinear_diag_sub_bound (B C : E →L[ℝ] E →L[ℝ] ℝ) (d:E) :
    |B d d-C d d|≤‖B-C‖*‖d‖^2 := by
  have H := (B-C).le_opNorm₂ d d
  simpa only [sub_apply,Real.norm_eq_abs,pow_two,mul_assoc] using H
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ShortLocalMinimum
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
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma chartCost_pair_contDiffAt_diagonal {a : M} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (fun q : Model n×Model n =>
      chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm q.1) q.2) (x,x) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  have hi : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ χ.symm x :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hx)
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨χ.symm x,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
    (zero_mem_injectivityDomain (n := n) (χ.symm x))
  simp only [riemannianExp_zero] at hc
  exact (hc.comp (x,x) ((hi.comp (x,x) contDiffAt_snd.contMDiffAt).prodMk
    (hi.comp (x,x) contDiffAt_fst.contMDiffAt))).contDiffAt
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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_DiagonalCostConvexity
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

lemma chartCost_diagonal_coercive {a : M} {z : Model n}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ∃ m>0, ∀ d : Model n, m*‖d‖^2 ≤
      fderiv ℝ (fderiv ℝ (chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm z))) z d d := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let x := χ.symm z
  have hx : x∈χ.source := χ.map_target hz
  have hxz : χ x=z := χ.right_inv hz
  change extChartAt 𝓘(ℝ,Model n) a x=z at hxz
  have hp := zero_mem_injectivityDomain (n := n) x
  obtain ⟨e,he,he0,hei,hinj⟩ := exists_smooth_chart_fiber_log hp
    (show riemannianExp x 0∈χ.source from by rwa [riemannianExp_zero])
  simp only [riemannianExp_zero,hxz] at he he0 hei hinj
  obtain ⟨m,hm,hbound⟩ := exists_norm_sq_lower_of_injective (fderiv ℝ e z) hinj
  refine ⟨m,hm,fun d => ?_⟩
  have hC : ContDiffAt ℝ 2 (normalCost (n := n) x 0) 0 :=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hzero : fderiv ℝ (normalCost (n := n) x 0) 0=0 := by
    rw [(normalCost_hasFDerivAt_zero hp).fderiv]
    simp only [neg_zero,map_zero]
  have heq : chartCost a x =ᶠ[𝓝 z] (fun w => normalCost (n := n) x 0 (e w)) := by
    filter_upwards [hei] with w hw
    simp only [normalCost,riemannianExp_zero,hw,chartCost]
  rw [heq.fderiv.fderiv_eq]
  have H := second_fderiv_comp_stationary (f := normalCost (n := n) x 0) (g := e)
    (he0.symm ▸ hC) (he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (by rwa [he0]) d d
  rw [H,he0]
  change m*‖d‖^2 ≤ normalHessian x 0 (fderiv ℝ e z d) (fderiv ℝ e z d)
  rw [←hessianValue_eq_normalHessian hp,hessianValue_zero]
  exact hbound d

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_EnvelopeKernelHessian
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma envelope_kernel_second_derivative {C : E×E → ℝ} {f : E → ℝ}
    {a : E → E} {p : E} {R : E →L[ℝ] E}
    (hC : ContDiffAt ℝ 2 C (a p,p))
    (ha : HasFDerivAt a R p)
    (hf : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q)
    (hsupport : ∀ᶠ q in 𝓝 p, ∀ᶠ v in 𝓝 q,
      f v≤f q+C (a q,v)-C (a q,q)) :
    ∀ d e:E, fderiv ℝ (fderiv ℝ f) p d e=
      fderiv ℝ (fderiv ℝ C) (a p,p) (R d,d) (0,e) := by
  let I : E →L[ℝ] E×E := (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)
  let G : E → E →L[ℝ] ℝ := fun q => (fderiv ℝ C (a q,q)).comp I
  have hmap := ha.prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := ((hC.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := fun q => (a q,q)) p hmap
  have hG := hd.clm_comp (hasFDerivAt_const I p)
  have heq : fderiv ℝ f =ᶠ[𝓝 p] G := by
    have hn := hmap.continuousAt.eventually (hC.eventually (by norm_num))
    filter_upwards [hf,hsupport,hn] with q hq hs hreg
    let g : E → ℝ := fun v => f q+C (a q,v)-C (a q,q)
    have hD := (hreg.differentiableAt (by norm_num)).hasFDerivAt.comp
      (f := fun v : E => (a q,v)) q
      ((hasFDerivAt_const (a q) q).prodMk (hasFDerivAt_id q))
    have hg : HasFDerivAt g (G q) q := by
      convert! (hD.const_add (f q)).sub_const (C (a q,q)) using 1
      all_goals try with_reducible_and_instances rfl
    rw [upper_contact_fderiv hq hg.differentiableAt hs (by dsimp [g] <;> ring)]
    exact hg.fderiv
  intro d e
  have H := congrArg (fun J : E →L[ℝ] E →L[ℝ] ℝ => J d e)
    (hG.congr_of_eventuallyEq heq).fderiv
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,map_zero,ContinuousLinearMap.comp_zero,
    add_zero,zero_add,add_apply,zero_apply,I] using H

lemma envelope_selector_injective_of_hessian_gap {C : E×E → ℝ} {f : E → ℝ}
    {a : E → E} {p : E} {R : E →L[ℝ] E}
    (hC : ContDiffAt ℝ 2 C (a p,p)) (ha : HasFDerivAt a R p)
    (hf : ∀ᶠ q in 𝓝 p,DifferentiableAt ℝ f q)
    (hsupport : ∀ᶠ q in 𝓝 p, ∀ᶠ v in 𝓝 q,
      f v≤f q+C (a q,v)-C (a q,q))
    {b k : ℝ} (hbk : b < k)
    (hupper : ∀ d:E,fderiv ℝ (fderiv ℝ f) p d d≤b*‖d‖^2)
    (hlower : ∀ d:E,k*‖d‖^2≤fderiv ℝ (fderiv ℝ C) (a p,p) (0,d) (0,d)) :
    Function.Injective R := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro d hd
  change R d = 0 at hd
  have H := envelope_kernel_second_derivative hC ha hf hsupport d d
  rw [hd] at H
  have hu := hupper d
  have hl := hlower d
  rw [H] at hu
  have hz : ‖d‖^2=0 := by nlinarith only [hu,hl,hbk,sq_nonneg ‖d‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ShortSelectorNonsingularity
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma second_fderiv_partial_snd {C : E×E → ℝ} {a b : E}
    (hC : ContDiffAt ℝ 2 C (a,b)) (v w:E) :
    fderiv ℝ (fderiv ℝ (fun z => C (a,z))) b v w =
      fderiv ℝ (fderiv ℝ C) (a,b) (0,v) (0,w) := by
  have hg : ContDiffAt ℝ 2 (fun z:E => (a,z)) b := contDiffAt_const.prodMk contDiffAt_id
  have hD : fderiv ℝ (fun z:E => (a,z)) = fun _ =>
      (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E) := by
    funext z
    exact ((hasFDerivAt_const a z).prodMk (hasFDerivAt_id z)).fderiv
  rw [second_fderiv_comp_with_acceleration hC hg,hD]
  rw [show fderiv ℝ (fun _ : E => (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) b=0 from
    (hasFDerivAt_const _ b).fderiv]
  simp only [ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,map_zero,add_zero]

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma exists_chart_cost_kernel_gap {a:M} {x:Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    let C := fun q:Model n×Model n => chartCost a
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1) q.2
    ∃ m>0, ∀ᶠ q in 𝓝 (x,x), ContDiffAt ℝ 2 C q ∧
      ∀ d:Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ C) q (0,d) (0,d) := by
  let : NormedAddCommGroup (Model n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (Model n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  dsimp only
  let F := fun y:Model n => chartCost (n := n) a ((extChartAt 𝓘(ℝ,Model n) a).symm y)
  have hc := chartCost_pair_contDiffAt_diagonal hx
  have hH : ContinuousAt (fun q:Model n×Model n => fderiv ℝ (fderiv ℝ (F q.1)) q.2) (x,x) :=
    (ContDiffAt.partial_snd_fderiv_two (f := F) hc).continuousAt
  obtain ⟨k,hk,hpos⟩ := chartCost_diagonal_coercive hx
  have hdiff : ContinuousAt (fun q:Model n×Model n =>
      fderiv ℝ (fderiv ℝ (F q.1)) q.2-fderiv ℝ (fderiv ℝ (F x)) x) (x,x) :=
    hH.sub continuousAt_const
  have hnorm := hdiff.norm
  have hn : ∀ᶠ q:Model n×Model n in 𝓝 (x,x),
      ‖fderiv ℝ (fderiv ℝ (F q.1)) q.2-fderiv ℝ (fderiv ℝ (F x)) x‖ < k/2 := by
    apply hnorm.eventually_lt continuousAt_const
    simpa only [Pi.sub_apply,Prod.fst,Prod.snd,sub_self,ContinuousLinearMap.opNorm_zero] using half_pos hk
  refine ⟨k/2,half_pos hk,?_⟩
  filter_upwards [hn,(hc.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)] with q hq hreg
  refine ⟨hreg,fun d => ?_⟩
  rw [←second_fderiv_partial_snd hreg d d]
  have hb := bilinear_diag_sub_bound (fderiv ℝ (fderiv ℝ (F q.1)) q.2)
    (fderiv ℝ (fderiv ℝ (F x)) x) d
  have hh := hpos d
  have hm := mul_le_mul_of_nonneg_right hq.le (sq_nonneg ‖d‖)
  have ha := (abs_le.mp hb).1
  change k/2*‖d‖^2≤fderiv ℝ (fderiv ℝ (F q.1)) q.2 d d
  linarith only [hh,hm,ha]

lemma actual_short_selector_injective_near {a:M} {x:Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ∃ m>0, ∀ᶠ q:Model n×Model n in 𝓝 (x,x),
      ∀ t : ℝ, 0 < t → ∀ u : M → ℝ, Continuous u →
      ∀ Y:Model n → Model n,∀ R:Model n →L[ℝ] Model n,
      Y q.2=q.1 → HasFDerivAt Y R q.2 →
      let χ := extChartAt 𝓘(ℝ,Model n) a
      let G := fun z:Model n => hopfLax t u (χ.symm z)
      (∀ᶠ z in 𝓝 q.2,G z=u (χ.symm (Y z))+chartCost a (χ.symm (Y z)) z/t) →
      (∀ᶠ z in 𝓝 q.2,DifferentiableAt ℝ G z) →
      ∀ b : ℝ, t*b < m →
      (∀ d:Model n,fderiv ℝ (fderiv ℝ G) q.2 d d≤b*‖d‖^2) →
      Function.Injective R := by
  obtain ⟨m,hm,H⟩ := exists_chart_cost_kernel_gap hx
  refine ⟨m,hm,?_⟩
  filter_upwards [H] with q hq
  intro t ht u hu Y R hY hR
  dsimp only
  intro hcontact hd b hb hupp
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let G := fun z:Model n => hopfLax t u (χ.symm z)
  let C := fun z:Model n×Model n => t⁻¹*chartCost a (χ.symm z.1) z.2
  have hc : ContDiffAt ℝ 2 C (Y q.2,q.2) := by
    rw [hY]
    exact contDiffAt_const.mul hq.1
  have hs : ∀ᶠ z in 𝓝 q.2,∀ᶠ v in 𝓝 z,
      G v≤G z+C (Y z,v)-C (Y z,z) := by
    filter_upwards [hcontact] with z hz
    apply Filter.Eventually.of_forall
    intro v
    have hv := hopfLax_le hu t (χ.symm v) (χ.symm (Y z))
    rw [cost_symm] at hv
    change G v≤u (χ.symm (Y z))+chartCost a (χ.symm (Y z)) v/t at hv
    change G z=u (χ.symm (Y z))+chartCost a (χ.symm (Y z)) z/t at hz
    dsimp only [C]
    rw [hz]
    convert hv using 1
    all_goals try with_reducible_and_instances rfl
    ring
  apply envelope_selector_injective_of_hessian_gap hc hR hd hs
    (show b < m/t from (lt_div_iff₀ ht).mpr (by linarith only [hb])) hupp
  intro d
  rw [hY]
  change (m/t)*‖d‖^2≤fderiv ℝ (fderiv ℝ (fun z:Model n×Model n =>
    t⁻¹*chartCost a (χ.symm z.1) z.2)) q (0,d) (0,d)
  rw [second_fderiv_const_mul]
  have HH := mul_le_mul_of_nonneg_left (hq.2 d) (inv_nonneg.mpr ht.le)
  convert HH using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumGoodCenters
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
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.good_centers_oai {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P) (hBc:Continuous Bc)
    (hx:Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hz:Tendsto (fun k=>(J.sample k).z (J.sampleIndex k (S.ν k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    {C:ℝ} (hG:∀ᶠ k in atTop,∀d,
      fderiv ℝ (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k))) d d ≤ C*‖d‖^2) :
    ∀ᶠ k in atTop,J.sampleCenter k (S.ν k)∉N := by
  let χ:=extChartAt 𝓘(ℝ,Model n) c
  obtain ⟨m,hm,H⟩:=actual_short_selector_injective_near (χ.map_source (mem_extChartAt_source c))
  have hτ:Tendsto (fun k=>(1-F.t k)*C) atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_self,zero_mul] using ((tendsto_const_nhds (x := (1:ℝ))).sub F.time).mul_const C
  filter_upwards [hG,(hx.prodMk_nhds hz).eventually H,hτ.eventually (gt_mem_nhds hm)]
    with k hGk hnear hsmall
  let j:=J.sampleIndex k (S.ν k)
  let T:=J.sample k
  obtain ⟨hy,_,_,_,hY,_,hnot,_,_,_,_⟩:=T.samples j
  have hcontact:∀ᶠ z in 𝓝 (T.z j),
      chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c z=
      modifiedDatum v α D (F.b k) Bc (χ.symm (χ (T.Y z)))+
        chartCost c (χ.symm (χ (T.Y z))) z/(1-F.t k) := by
    filter_upwards [T.openRegion.mem_nhds (T.sampleInRegion j)] with z hz
    have he:χ.symm (χ (T.Y z))=T.Y z:=χ.left_inv (T.actual z hz).1
    rw [he]
    simpa only [chartCost,cost_symm] using ((T.actual z hz).2.2.1 (T.Y z)).mpr rfl
  have hd:∀ᶠ z in 𝓝 (T.z j),
      DifferentiableAt ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c) z := by
    filter_upwards [T.openRegion.mem_nhds (T.sampleInRegion j)] with z hz
    exact T.centerDifferentiable z hz
  have hinj:Function.Injective (fderiv ℝ (fun z=>χ (T.Y z)) (T.z j)) :=
    hnear (1-F.t k) (by linarith [(F.prefixTime k).2])
      (modifiedDatum v α D (F.b k) Bc) (continuous_modifiedDatum hv α D (F.b k) hBc)
      (fun z=>χ (T.Y z)) _ rfl hY hcontact hd C hsmall hGk
  apply hnot
  intro hzero
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) (LinearMap.ker_eq_bot.mpr hinj)

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.MaximumDiagonal.good_centers_oai.{u_1} := @OAI.WeakMTWTransport.MaximumDiagonal.good_centers_oai.{u_1}
