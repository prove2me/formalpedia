-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.actual_sample_pole_matrix
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:41:18.55521+00:00
-- url     : https://prove2.me/submissions/9622175c-1bef-441a-ada5-b4cdbf193ace

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
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_actualPole_kernel
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_actualPole_taylor
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_modified_active_lower_jet_nonneg

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_GraphInverse
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

lemma WeakMTW.graphHomeomorph_inverse_pole (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1) (z:M) :
    ((hmtw.graphHomeomorph hv ht ht1).symm z).1.1=hopfPole (n := n) t (cTransform v) z := by
  let q := (hmtw.graphHomeomorph hv ht ht1).symm z
  have H := congrArg Bundle.TotalSpace.proj (hmtw.hopfLax_backward_flow hv ht ht1 q)
  change hopfPole (n := n) t (cTransform v)
    ((hmtw.graphHomeomorph hv ht ht1) q)=q.1.1 at H
  simpa only [q,Homeomorph.apply_symm_apply] using H.symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SamplePoleDerivative
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

lemma WeakMTW.continuous_hopfPole (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    Continuous (hopfPole (n := n) t (cTransform v)) := by
  have H := (FiberBundle.continuous_proj (Model n)
    (TangentSpace 𝓘(ℝ,Model n))).comp
      (continuous_subtype_val.comp (hmtw.graphHomeomorph hv ht ht1).symm.continuous)
  exact H.congr (fun z=>hmtw.graphHomeomorph_inverse_pole hv ht ht1 z)

lemma WeakMTW.exists_actual_normal_pole_derivative
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x a c : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hz : riemannianExp x (t • p)∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hpole : hopfPole (n := n) t (cTransform v) (riemannianExp x (t • p))=x)
    (hD : DifferentiableAt ℝ
      (fun w : Model n => extChartAt 𝓘(ℝ,Model n) c
        (hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm w)))
      (extChartAt 𝓘(ℝ,Model n) a (riemannianExp x (t • p)))) :
    ∃ e : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x,
    ∃ R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
      HasFDerivAt e R p ∧ e p=0 ∧
      ∀ᶠ q in 𝓝 p,riemannianExp x (e q)=
        hopfPole (n := n) t (cTransform v) (riemannianExp x (t • q)) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let ψ := extChartAt 𝓘(ℝ,Model n) c
  let P := hopfPole (n := n) t (cTransform v)
  let F : Model n → Model n := fun w=>ψ (P (χ.symm w))
  let z := riemannianExp x (t • p)
  let Z : V → Model n := fun q=>χ (riemannianExp x (t • q))
  let S : V →L[ℝ] V := t • ContinuousLinearMap.id ℝ V
  have hc : ContMDiffAt 𝓘(ℝ,V) 𝓘(ℝ,Model n) ∞
      (fun q:V=>riemannianExp x (t • q)) p :=
    (contMDiff_riemannianExp_fiber x (t • p)).comp p S.contDiff.contMDiff.contMDiffAt
  have hZ : ContDiffAt ℝ ∞ Z p :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ,Model n)) (by
      simpa only [extChartAt_source] using hz)).comp p hc).contDiffAt
  have hFz : F (Z p)=ψ x := by
    dsimp [F,Z]; rw [χ.left_inv hz]; exact congrArg ψ hpole
  obtain ⟨L,hL,hL0,hLi,hLin⟩ := exists_smooth_chart_fiber_log
    (zero_mem_injectivityDomain (n := n) x) (by simpa only [riemannianExp_zero] using hx)
  simp only [riemannianExp_zero] at hL hL0 hLi hLin
  let e : V → V := fun q=>L (F (Z q))
  have hDZ : DifferentiableAt ℝ (fun q=>F (Z q)) p :=
    (show DifferentiableAt ℝ F (Z p) from hD).comp (f := Z) p (hZ.differentiableAt (by simp))
  have hDe : DifferentiableAt ℝ e p :=
    (show DifferentiableAt ℝ L (F (Z p)) from hFz ▸ hL.differentiableAt (by simp)).comp p hDZ
  refine ⟨e,fderiv ℝ e p,hDe.hasFDerivAt,?_,?_⟩
  · dsimp [e]; rw [hFz]; exact hL0
  have hexp : ContinuousAt (fun q:V=>riemannianExp x (t • q)) p := hc.continuousAt
  have hP : ContinuousAt (fun q:V=>P (riemannianExp x (t • q))) p :=
    (hmtw.continuous_hopfPole hv ht ht1).continuousAt.comp hexp
  have hcZ : ∀ᶠ q in 𝓝 p,riemannianExp x (t • q)∈χ.source :=
    hexp.eventually ((isOpen_extChartAt_source a).mem_nhds hz)
  have hcP : ∀ᶠ q in 𝓝 p,P (riemannianExp x (t • q))∈ψ.source :=
    hP.eventually (show ψ.source∈𝓝 (P (riemannianExp x (t • p))) from by
      change ψ.source∈𝓝 (hopfPole (n := n) t (cTransform v) (riemannianExp x (t • p)))
      rw [hpole]; exact (isOpen_extChartAt_source c).mem_nhds hx)
  have hlog : ∀ᶠ q in 𝓝 p,riemannianExp x (L (F (Z q)))=ψ.symm (F (Z q)) :=
    hDZ.continuousAt.eventually (hFz ▸ hLi)
  filter_upwards [hcZ,hcP,hlog] with q hq hpq hlq
  change riemannianExp x (L (F (Z q)))=P (riemannianExp x (t • q))
  rw [hlq]
  dsimp [F,Z]
  rw [χ.left_inv hq,ψ.left_inv hpq]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_UniformRegularSplit
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

lemma prefixAction_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x) :
    ContDiffAt ℝ ∞ (prefixAction x t) (0,p) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have he := contMDiff_riemannianExp_fiber (n := n) x
  have hu : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x q.1) (0,p) :=
    (he _).comp (0,p) contDiffAt_fst.contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x (t • q.2)) (0,p) :=
    (he _).comp (0,p) (show ContDiffAt ℝ ∞ (fun q : V×V => t • q.2) (0,p) from by fun_prop).contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨x,t • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:V),riemannianExp x (t • p)) := by
    simpa only [riemannianExp_zero] using hc
  exact ((hc'.comp (0,p) (hu.prodMk hv)).contDiffAt.div_const t)

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

lemma prefixAction_source_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hp : t • p ∈ injectivityDomain x)
    (a : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (prefixAction x t) (0,p) (a,0) = -inner ℝ p a := by
  have hnc := ((normalCost_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have H := hnc.mul_const t⁻¹
  have hp₀ := (hasFDerivAt_id (𝕜 := ℝ) (0 : TangentSpace 𝓘(ℝ,Model n) x)).prodMk
    (hasFDerivAt_const p (0 : TangentSpace 𝓘(ℝ,Model n) x))
  have H' : HasFDerivAt (fun u => prefixAction x t (u,p))
      (t⁻¹ • fderiv ℝ (normalCost x (t • p)) 0) 0 := by
    simpa only [prefixAction,normalCost,div_eq_mul_inv] using H
  have hB := (prefixAction_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heq := (hB.hasFDerivAt.comp (f := fun u => (u,p)) 0 hp₀).unique H'
  have hh := congrArg (fun A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => A a) heq
  change fderiv ℝ (prefixAction x t) (0,p) (a,0) =
    t⁻¹ * fderiv ℝ (normalCost x (t • p)) 0 a at hh
  rw [normalCost_fderiv_zero hp,real_inner_smul_left] at hh
  rw [hh]
  field_simp

lemma prefixAction_mixed {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hp : t • p ∈ injectivityDomain x)
    (a d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (0,d) (a,0) = -inner ℝ d a := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hL : HasFDerivAt (fun v : V => ((0:V),v))
      ((0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)) p :=
    (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := (((hC.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun v : V => ((0:V),v)) p hL).clm_apply
      (hasFDerivAt_const (a,(0:V)) p)
  have heq : (fun v : V => fderiv ℝ (prefixAction x t) (0,v) (a,0)) =ᶠ[𝓝 p]
      (fun v => -inner ℝ v a) := by
    have hn := (continuous_const_smul t).continuousAt.eventually
      ((isOpen_injectivityDomain x).mem_nhds hp)
    filter_upwards [hn] with v hv
    exact prefixAction_source_gradient ht hv a
  have hi : HasFDerivAt (fun v : V => -inner ℝ v a) (-(innerSL ℝ a)) p := by
    convert! ((innerSL ℝ a).hasFDerivAt (x := p)).neg using 1
    all_goals try with_reducible_and_instances rfl
    funext v; exact congrArg Neg.neg (real_inner_comm a v)
  have H := congrArg (fun A : V →L[ℝ] ℝ => A d)
    ((hd.congr_of_eventuallyEq heq.symm).unique hi)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,zero_apply,map_zero,add_zero,zero_add,add_apply,
    ContinuousLinearMap.comp_zero,Function.comp_apply,
    ContinuousLinearMap.flip_apply,neg_apply,innerSL_apply_apply,real_inner_comm] using H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PrefixActionJets
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

lemma prefixAction_endpoint_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x)
    (d e : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (0,d) (0,e) = t*inner ℝ d e := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he := ((prefixAction_axis_near hp).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  let L : V →L[ℝ] V×V := (0:V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)
  have H := second_fderiv_comp_affine L 0 p
    (by simpa only [L,ContinuousLinearMap.prod_apply,zero_apply,
      ContinuousLinearMap.id_apply,zero_add] using hC) d e
  simp only [L,ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,zero_add] at H
  rw [←H,he]
  have hg : fderiv ℝ (fun v : V => t*(‖v‖^2/2)) =
      (fun v => t • innerSL ℝ v) := by
    funext v
    exact ((half_norm_sq_hasFDerivAt v).const_smul t).fderiv
  rw [hg]
  have hD : HasFDerivAt (fun v : V => t • innerSL ℝ v) (t • innerSL ℝ) p := by
    convert! ((innerSL ℝ).hasFDerivAt (x := p)).const_smul t using 1
    all_goals try with_reducible_and_instances rfl
  rw [hD.fderiv]
  rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_EnvelopePole
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

lemma envelope_pole_second_derivative {C : E×E → ℝ} {f : E → ℝ}
    {a : E → E} {p : E} {R : E →L[ℝ] E} {t : ℝ}
    (hC : ContDiffAt ℝ 2 C (0,p))
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (hf : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q)
    (hsupport : ∀ᶠ q in 𝓝 p, ∀ᶠ v in 𝓝 q,
      f v≤f q+C (a q,v)-C (a q,q))
    (hqq : ∀ d e:E, fderiv ℝ (fderiv ℝ C) (0,p) (0,d) (0,e)=t*inner ℝ d e)
    (haq : ∀ d e:E, fderiv ℝ (fderiv ℝ C) (0,p) (d,0) (0,e) = -inner ℝ d e) :
    HasFDerivAt (fderiv ℝ f) (t • innerSL ℝ-(innerSL ℝ).comp R) p := by
  let I : E →L[ℝ] E×E := (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)
  let G : E → E →L[ℝ] ℝ := fun q => (fderiv ℝ C (a q,q)).comp I
  have hmap := ha.prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hC' : ContDiffAt ℝ 2 C (a p,p) := by rwa [ha0]
  have hd := ((hC'.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := fun q => (a q,q)) p hmap
  have hG := hd.clm_comp (hasFDerivAt_const I p)
  have heq : fderiv ℝ f =ᶠ[𝓝 p] G := by
    have hn := hmap.continuousAt.eventually (hC'.eventually (by norm_num))
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
  apply (hG.congr_of_eventuallyEq heq).congr_fderiv
  ext d e
  simp only [ha0,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_zero,
    zero_add,zero_apply,sub_apply,smul_apply,smul_eq_mul,
    innerSL_apply_apply,I]
  have he : (R d,d)=((R d,0):E×E)+(0,d) := by simp
  rw [he,map_add,add_apply,haq,hqq]
  change -inner ℝ (R d) e+t*inner ℝ d e = t*inner ℝ d e-inner ℝ (R d) e
  ring
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_ActualPole
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

lemma WeakMTW.hopfPole_minimizer (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (z:M) :
    hopfLax t u z=u (hopfPole (n := n) t u z)+cost (hopfPole (n := n) t u z) z/t := by
  rw [hdual.1] at hu ⊢
  obtain ⟨q,hq⟩ := surjective_graphProjection (n := n) hu ht z
  have H := congrArg Bundle.TotalSpace.proj (hmtw.hopfLax_backward_flow hv ht ht1 q)
  have He : hopfPole (n := n) t (cTransform v) z=q.1.1 := by
    change hopfPole (n := n) t (cTransform v) (graphProjection (cTransform v) t q)=q.1.1 at H
    rwa [hq] at H
  rw [He,←hq]
  exact hmtw.hopfLax_graph_value hv ht ht1 q

lemma WeakMTW.prefix_hopfLax_differentiable (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (x:M) :
    Differentiable ℝ (fun q : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • q))) := by
  intro q
  have he := (contMDiff_riemannianExp_fiber (n := n) x (t • q)).mdifferentiableAt (by simp)
  have hl : MDifferentiableAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x)
      𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) (fun q => t • q) q :=
    (show ContDiffAt ℝ ∞ (fun q : TangentSpace 𝓘(ℝ,Model n) x => t • q) q from by
      fun_prop).contMDiffAt.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact ((hmtw.mdifferentiable_hopfLax hu hv hdual ht ht1 _).comp q
    (he.comp q hl)).differentiableAt

lemma WeakMTW.actualPole_supports (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    (ha : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    ∀ᶠ q in 𝓝 p, ∀ᶠ w in 𝓝 q,
      hopfLax t u (riemannianExp x (t • w))≤
        hopfLax t u (riemannianExp x (t • q))+
          prefixAction x t (a q,w)-prefixAction x t (a q,q) := by
  filter_upwards [ha] with q hq
  apply Filter.Eventually.of_forall
  intro w
  have H := hmtw.hopfPole_minimizer hu hv hdual ht ht1 (riemannianExp x (t • q))
  rw [←hq] at H
  have Hw := hopfLax_le hu t (riemannianExp x (t • w)) (riemannianExp x (a q))
  dsimp [prefixAction]
  linarith

lemma WeakMTW.actualPole_second_derivative (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (harep : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    HasFDerivAt (fderiv ℝ (fun q : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • q))))
      (t • innerSL ℝ-(innerSL ℝ).comp R) p := by
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  apply envelope_pole_second_derivative hC ha ha0
    (Filter.Eventually.of_forall (hmtw.prefix_hopfLax_differentiable hu hv hdual ht ht1 x))
    (hmtw.actualPole_supports hu hv hdual ht ht1 harep)
    (prefixAction_endpoint_hessian hp)
  intro d e
  rw [hC.isSymmSndFDerivAt (by norm_num) |>.eq]
  rw [prefixAction_mixed ht.ne' hp]
  exact congrArg Neg.neg (real_inner_comm d e)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ModifiedActiveLowerJet
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

lemma active_contact_biconjugate {v : M → ℝ} (hv : Continuous v) {x y : M}
    (hactive : contactGap (cTransform v) v x y=0) :
    cTransform (cTransform v) y=v y ∧
      contactGap (cTransform v) (cTransform (cTransform v)) x y=0 := by
  have hle := cTransform_cTransform_le hv y
  have hlo := cTransform_gap_nonneg (continuous_cTransform hv) y x
  rw [contactGap,cost_symm y x] at hlo
  have hact := hactive
  rw [contactGap] at hact
  have he : cTransform (cTransform v) y=v y := by linarith only [hle,hlo,hact]
  exact ⟨he,by simpa only [contactGap,he] using hactive⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SampleJetData
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
lemma exists_actual_uniform_regular_split_after {t:ℝ} (ht : 0<t) (ht1 : t<1) :
    ∃ s:ℝ,t < s ∧ s<1 ∧ ∀ x:M,∀ p:TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → s • p∈injectivityDomain x ∧
      (1-s) • (sprayFlow s (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).2∈
        injectivityDomain (sprayFlow s (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  have H : ∀ᶠ s in 𝓝[<] (1:ℝ),t < s ∧ s<1 ∧ ∀ x:M,
      ∀ p:TangentSpace 𝓘(ℝ,Model n) x,‖p‖≤Metric.diam (univ:Set M) →
        (1-s) • (sprayFlow s (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).2∈
          injectivityDomain (sprayFlow s (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1 := by
    filter_upwards [(uniformly_shifted_injectivityDomain_near_one
      (n := n) (M := M) (Metric.diam (univ:Set M))).filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds ht1).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
      with s hs hst hs1
    exact ⟨hst,hs1,hs⟩
  obtain ⟨s,hst,hs1,hs⟩ := H.exists
  exact ⟨s,hst,hs1,fun x p hp=>⟨contracted_minimizer_mem_injectivityDomain hp
    (ht.trans hst) hs1,hs x p (minimizing_norm_le_diam hp)⟩⟩

lemma WeakMTW.actual_sample_pole_matrix_oai (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {x a c : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈normalSubdifferential (n := n) (cTransform v) x)
    (hz : riemannianExp x (t • p)∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hD : DifferentiableAt ℝ
      (fun w : Model n => extChartAt 𝓘(ℝ,Model n) c
        (hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm w)))
      (extChartAt 𝓘(ℝ,Model n) a (riemannianExp x (t • p)))) :
    let V := TangentSpace 𝓘(ℝ,Model n) x
    let I : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
    let L : V →L[ℝ] V →L[ℝ] ℝ := t • I - fderiv ℝ (fderiv ℝ
      (fun q:V=>hopfLax t (cTransform v) (riemannianExp x (t • q)))) p
    DifferentiableAt ℝ (fderiv ℝ
      (fun q:V=>hopfLax t (cTransform v) (riemannianExp x (t • q)))) p ∧
    (∀ d:V,0≤L d d) ∧ (∀ d e:V,L d e=L e d) ∧
    (∀ q∈activeLogs v x,∀ d:V,L (q-p) d=0) ∧
    (∀ (ι:Type) [Fintype ι] (pj:ι → V) (w:ι → ℝ),
      (∀ j,0≤w j) → (∑ j,w j=1) → (∑ j,w j • pj j=p) →
      (∀ j,pj j∈activeLogs v x) → ∀ i,0<w i →
      HasLowerSecondTaylor (fun d:V=>v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2)
        0 (w i • L)) := by
  dsimp only
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let : NormedAddCommGroup (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let q : subgradientGraph (n := n) (cTransform v) := ⟨⟨x,p⟩,hp⟩
  have hpole : hopfPole (n := n) t (cTransform v) (riemannianExp x (t • p))=x := by
    exact congrArg Bundle.TotalSpace.proj (hmtw.hopfLax_backward_flow hv ht ht1 q)
  obtain ⟨e,R,he,he0,herep⟩ := hmtw.exists_actual_normal_pole_derivative hv ht ht1 hz hx hpole hD
  have hpre := hmtw.active_hull_precut hv ht ht1 x p
    (normalSubdifferential_subset_active_hull hv x hp)
  have hdual : IsCostDualPair (cTransform v) (cTransform (cTransform v)) :=
    ⟨(cTransform_triple hv).symm,rfl⟩
  have HD' := hmtw.actualPole_second_derivative (continuous_cTransform hv)
    (continuous_cTransform (continuous_cTransform hv)) hdual ht ht1 hpre he he0 herep
  have HD := HD'.fderiv
  rw [HD,sub_sub_cancel]
  have H := hmtw.actualPole_taylor (continuous_cTransform hv)
    (continuous_cTransform (continuous_cTransform hv)) hdual ht ht1 hpre he he0 herep
  obtain ⟨s,hts,hs1,hs⟩ := exists_actual_uniform_regular_split_after (n := n) (M := M) ht ht1
  refine ⟨HD'.differentiableAt,H.2.1,?_,?_,?_⟩
  · intro d f
    change inner ℝ (R d) f=inner ℝ (R f) d
    exact (H.2.2 d f).trans (real_inner_comm (R f) d)
  · intro r hr d
    have hk := hmtw.actualPole_kernel (continuous_cTransform hv)
      (continuous_cTransform (continuous_cTransform hv)) hdual ht ht1 (ht.trans hts) hs1
      hpre hr.1 (active_contact_biconjugate hv hr.2).2 (hs x r hr.1).1 (hs x r hr.1).2
      he he0 herep
    simp only [ContinuousLinearMap.comp_apply,hk,map_zero,zero_apply]
  · intro ι _ pj w hw hw1 hbar ha i hi
    exact hmtw.modified_active_lower_jet_nonneg hv ht hts hs1 pj w hw hw1 i hi
      (fun j=>(ha j).1) (fun j=>(ha j).2) (fun j=>(hs x (pj j) (ha j).1).1)
      (fun j=>(hs x (pj j) (ha j).1).2) (hbar ▸ he) (hbar ▸ he0) (hbar ▸ herep)

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.actual_sample_pole_matrix_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.actual_sample_pole_matrix_oai.{u_1}
