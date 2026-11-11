-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_true_matrix
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:39:00.572005+00:00
-- url     : https://prove2.me/submissions/9fd48f10-a5bc-4e82-ba2f-115a20bdd86b

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
import Definitions.Def_OAIQ232A028
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_uniform_outer_normal_det_bound_second

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_FullSet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma bilinear_isBigO_norm_mul {α : Type*} (L : Filter α)
    (B : E →L[ℝ] F →L[ℝ] G) (u : α → E) (v : α → F) :
    (fun x => B (u x) (v x)) =O[L] (fun x => ‖u x‖*‖v x‖) := by
  apply Asymptotics.IsBigO.of_bound ‖B‖
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      mul_assoc] using B.le_opNorm₂ (u x) (v x))

lemma bilinear_remainder_of_hasFDerivAt {a : E → F} {A : E →L[ℝ] F}
    (ha : HasFDerivAt a A 0) (ha0 : a 0=0) (B : F →L[ℝ] F →L[ℝ] ℝ) :
    (fun h => B (a h) (a h)-B (A h) (A h)) =o[𝓝 0] (fun h : E => ‖h‖^2) := by
  have hR : (fun h => a h-A h) =o[𝓝 0] (fun h : E => h) := by
    simpa only [zero_add,ha0,sub_zero] using hasFDerivAt_iff_isLittleO_nhds_zero.mp ha
  have hO : a =O[𝓝 0] (fun h : E => h) := by
    simpa only [ha0,sub_zero] using ha.isBigO_sub
  have hA : (fun h : E => A h) =O[𝓝 0] (fun h => h) := A.isBigO_id _
  have h1 := (bilinear_isBigO_norm_mul (𝓝 (0:E)) B (fun h => a h-A h) a).trans_isLittleO
    (hR.norm_left.norm_right.mul_isBigO hO.norm_left.norm_right)
  have h2 := (bilinear_isBigO_norm_mul (𝓝 (0:E)) B (fun h => A h) (fun h => a h-A h)).trans_isLittleO
    (hA.norm_left.norm_right.mul_isLittleO hR.norm_left.norm_right)
  have he : (fun h => B (a h) (a h)-B (A h) (A h)) =
      (fun h => B (a h-A h) (a h)+B (A h) (a h-A h)) := by
    funext h
    simp only [map_sub,_root_.sub_apply]
    ring
  rw [he]
  simpa only [pow_two] using h1.add h2

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_LowerTaylor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HasLowerSecondTaylor.mono {f g : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasLowerSecondTaylor f l B)
    (he : f 0=g 0) (hle : f≤ᶠ[𝓝 0] g) : HasLowerSecondTaylor g l B := by
  intro ε hε
  filter_upwards [hf ε hε,hle] with h hh hfg
  rw [←he]
  exact hh.trans hfg

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_LowerTaylorComposition
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HasLowerSecondTaylor.comp_stationary {f : F → ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hf : HasLowerSecondTaylor f 0 B)
    {a : E → F} {A : E →L[ℝ] F} (ha : HasFDerivAt a A 0) (ha0 : a 0=0) :
    HasLowerSecondTaylor (fun h => f (a h)) 0 (pullBilinear B A) := by
  have hO : a =O[𝓝 0] (fun h : E => h) := by
    simpa only [ha0,sub_zero] using ha.isBigO_sub
  obtain ⟨C,hC,HC⟩ := hO.exists_pos
  have ht : Tendsto a (𝓝 0) (𝓝 0) := ha0 ▸ ha.continuousAt
  intro ε hε
  have hδ : 0 < ε/(2*C^2) := div_pos hε (by positivity)
  have hB := (bilinear_remainder_of_hasFDerivAt ha ha0 B).def hε
  filter_upwards [ht.eventually (hf _ hδ),HC.bound,hB] with h hh haB hb
  simp only [zero_apply,add_zero] at hh ⊢
  rw [ha0,pullBilinear_apply]
  have hb' : |B (a h) (a h)-B (A h) (A h)| ≤ ε*‖h‖^2 := by
    simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using hb
  have hsq : ‖a h‖^2 ≤ C^2*‖h‖^2 := by
    nlinarith only [sq_nonneg (C*‖h‖-‖a h‖),haB,norm_nonneg (a h),
      mul_nonneg hC.le (norm_nonneg h)]
  have hsq' := mul_le_mul_of_nonneg_left hsq (le_of_lt hδ)
  have he : ε/(2*C^2)*(C^2*‖h‖^2)=(ε/2)*‖h‖^2 := by
    field_simp [hC.ne']
  rw [he] at hsq'
  linarith only [hh,(abs_le.mp hb').1,hsq']

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_TwoSidedFiberLog
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section TwoSidedFiberLog
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_coordinate_exp_inverse_of_nonconjugate {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : Function.Injective (fderiv ℝ
      (fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p)
        (riemannianExp (n := n) x v)) p)) :
    ∃ e : OpenPartialHomeomorph (TangentSpace 𝓘(ℝ,Model n) x) (Model n),
      (e : TangentSpace 𝓘(ℝ,Model n) x → Model n) =
        (fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) (riemannianExp (n := n) x v)) ∧
      p ∈ e.source ∧ ContDiffAt ℝ ∞ e.symm (e p) := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  let f := fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) (riemannianExp (n := n) x v)
  have hf : ContDiffAt ℝ ∞ f p :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞
      (extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p)) (riemannianExp (n := n) x p) from
      contMDiffAt_extChartAt).comp p (contMDiff_riemannianExp_fiber x p)).contDiffAt
  let D := fderiv ℝ f p
  have hi : Function.Injective D := hp
  let τ := trivializationAt (Model n) (fun b : M => TangentSpace 𝓘(ℝ,Model n) b) x
  let L : TangentSpace 𝓘(ℝ,Model n) x ≃L[ℝ] Model n :=
    τ.continuousLinearEquivAt ℝ x (mem_baseSet_trivializationAt (Model n) _ x)
  have hs : Function.Surjective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank L.toLinearEquiv.finrank_eq).mp hi
  let A := ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs)
  have hd : HasFDerivAt f (A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n) p :=
    (hf.differentiableAt (by simp)).hasFDerivAt
  let e := hf.toOpenPartialHomeomorph f hd (by simp)
  have he : p ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hd (by simp)
  refine ⟨e,rfl,he,?_⟩
  exact hf.to_localInverse hd (by simp)

lemma exists_smooth_two_sided_fiber_log_of_nonconjugate {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : Function.Injective (fderiv ℝ
      (fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p)
        (riemannianExp (n := n) x v)) p)) :
    ∃ L : M → TangentSpace 𝓘(ℝ,Model n) x,
      ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) ∞ L
        (riemannianExp x p) ∧
      L (riemannianExp x p)=p ∧
      (∀ᶠ y in 𝓝 (riemannianExp x p), riemannianExp x (L y)=y) ∧
      (∀ᶠ v in 𝓝 p, L (riemannianExp x v)=v) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  let d := extChartAt 𝓘(ℝ,Model n) y
  obtain ⟨e,he,hpe,hei⟩ := exists_coordinate_exp_inverse_of_nonconjugate hp
  have hep : e p=d y := by rw [he]
  let L : M → V := fun z => e.symm (d z)
  have hL : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L y :=
    (show ContDiffAt ℝ ∞ e.symm (d y) from hep ▸ hei).contMDiffAt.comp y
      (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y from contMDiffAt_extChartAt)
  have hLy : L y=p := by dsimp [L]; rw [←hep,e.left_inv hpe]
  refine ⟨L,hL,hLy,?_,?_⟩
  · have ht : ∀ᶠ z in 𝓝 y, d z∈e.target :=
      (continuousAt_extChartAt y).eventually (e.open_target.mem_nhds (hep ▸ e.map_source hpe))
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
  · filter_upwards [e.open_source.mem_nhds hpe] with v hv
    change e.symm (d (riemannianExp x v))=v
    rw [←show e v=d (riemannianExp x v) from congrFun he v]
    exact e.left_inv hv

end TwoSidedFiberLog
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_EndpointLowerJet
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section EndpointLowerJet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_normal_endpoint_log_of_nonconjugate {z y : M}
    {q : TangentSpace 𝓘(ℝ,Model n) z} (hend : riemannianExp z q=y)
    (hq : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z q) (riemannianExp z v)) q)) :
    ∃ e : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) z,
      ContDiffAt ℝ ∞ e 0 ∧ e 0=q ∧
      (∀ᶠ w in 𝓝 0, riemannianExp z (e w)=riemannianExp y w) ∧
      Function.Injective (fderiv ℝ e 0) := by
  let V := TangentSpace 𝓘(ℝ,Model n) z
  let W := TangentSpace 𝓘(ℝ,Model n) y
  obtain ⟨log,hlog,hlogq,hlogi,_⟩ := exists_smooth_two_sided_fiber_log_of_nonconjugate hq
  rw [hend] at hlog hlogq hlogi
  let e : W → V := fun w => log (riemannianExp y w)
  have he : ContDiffAt ℝ ∞ e 0 :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ log (riemannianExp y 0) from
      by simpa only [riemannianExp_zero] using hlog).comp 0
      (contMDiff_riemannianExp_fiber y 0)).contDiffAt
  have he0 : e 0=q := by dsimp [e]; rw [riemannianExp_zero,hlogq]
  have hei : ∀ᶠ w in 𝓝 (0:W), riemannianExp z (e w)=riemannianExp y w :=
    (show ContinuousAt (riemannianExp y) (0:W) from (continuous_riemannianExp y).continuousAt).eventually
      (by simpa only [riemannianExp_zero] using hlogi)
  let χ := extChartAt 𝓘(ℝ,Model n) y
  let F : V → Model n := fun v => χ (riemannianExp z v)
  let G : W → Model n := fun w => χ (riemannianExp y w)
  have hF : ContDiffAt ℝ ∞ F q :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ χ (riemannianExp z q) from
      by rw [hend]; exact contMDiffAt_extChartAt).comp q
      (contMDiff_riemannianExp_fiber z q)).contDiffAt
  have hEq : (fun w => F (e w)) =ᶠ[𝓝 (0:W)] G := hei.mono (fun _ hw => congrArg χ hw)
  have hD := hEq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp 0 (by simpa only [he0] using hF.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (he.differentiableAt (by simp)),he0] at hD
  have hG : Function.Injective (fderiv ℝ G 0) := by
    simpa only [G,χ,riemannianExp_zero] using
      riemannianExp_interior_nonconjugate (zero_mem_injectivityDomain (n := n) y)
  refine ⟨e,he,he0,hei,?_⟩
  have hcomp : Function.Injective ((fderiv ℝ F q).comp (fderiv ℝ e 0)) := by
    rw [hD]
    exact hG
  exact Function.Injective.of_comp (f := fderiv ℝ F q) (g := fderiv ℝ e 0) hcomp

end EndpointLowerJet
end WeakMTWTransport

end

end

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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_FixedJoinSpectrum
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
section FixedJoinSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]

local instance tangentFiniteSpectrum_r1e9747_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma tangent_finrank (x : M) : finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x)=n :=
  finrank_euclideanSpace_fin
end FixedJoinSpectrum
end WeakMTWTransport

end

end

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

lemma expJacobian_eq_normal_endpoint {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p)}
    (hL : DifferentiableAt ℝ L p) (hLp : L p=0)
    (hLi : ∀ᶠ v in 𝓝 p, riemannianExp (riemannianExp x p) (L v)=riemannianExp x v) :
    expJacobian x p=(fderiv ℝ L p).toLinearMap.normDet := by
  unfold expJacobian
  apply congrArg LinearMap.normDet
  ext k
  exact (normal_endpoint_derivative_eq hL hLp hLi k).symm

lemma exists_normal_endpoint_coordinates (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    ∃ L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p),
      ContDiffAt ℝ ∞ L p ∧ L p=0 ∧
      (∀ᶠ v in 𝓝 p, riemannianExp (riemannianExp x p) (L v)=riemannianExp x v) := by
  let y := riemannianExp x p
  obtain ⟨N,hN,hN0,hNi⟩ := exists_smooth_fiber_log (zero_mem_injectivityDomain (n := n) y)
  simp only [riemannianExp_zero] at hN hN0 hNi
  refine ⟨(fun v => N (riemannianExp x v)),?_,hN0,?_⟩
  · exact (hN.comp p (contMDiff_riemannianExp_fiber x p)).contDiffAt
  · exact (continuous_riemannianExp x).continuousAt.eventually hNi
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalEndpointInverse
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
section NormalEndpointInverse
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance localInst_r1e9747_1 (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma exists_normal_endpoint_inverse {x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    (hp:Function.Injective (fderiv ℝ (fun v=>extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p)) :
    ∃ (e:TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p) → TangentSpace 𝓘(ℝ,Model n) x)
      (C:TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p)),
      ContDiffAt ℝ ∞ e 0 ∧ e 0=p ∧
      (∀ᶠ w in 𝓝 0,riemannianExp x (e w)=riemannianExp (riemannianExp x p) w) ∧
      Function.Injective C ∧ C.comp (fderiv ℝ e 0)=ContinuousLinearMap.id ℝ _ ∧
      (fderiv ℝ e 0).comp C=ContinuousLinearMap.id ℝ _ ∧
      expJacobian x p=C.toLinearMap.normDet := by
  let y:=riemannianExp x p
  let E:=TangentSpace 𝓘(ℝ,Model n) x
  let F:=TangentSpace 𝓘(ℝ,Model n) y
  obtain ⟨e,he,he0,hei,heD⟩:=exists_smooth_normal_endpoint_log_of_nonconjugate (y:=y) rfl hp
  obtain ⟨R,hR,hR0,hRi⟩:=exists_normal_endpoint_coordinates x p
  let C:E →L[ℝ] F:=fderiv ℝ R p
  let J:F →L[ℝ] E:=fderiv ℝ e 0
  have hJD:HasFDerivAt e J 0:= (he.differentiableAt (by simp)).hasFDerivAt
  have hCD:HasFDerivAt R C p:= (hR.differentiableAt (by simp)).hasFDerivAt
  have hn:injectivityDomain y∈𝓝 (0:F):=
    (isOpen_injectivityDomain y).mem_nhds (zero_mem_injectivityDomain y)
  have hRcomp:ContinuousAt (fun w=>R (e w)) 0:=
    (show ContinuousAt R (e 0) from by rw [he0]; exact hR.continuousAt).comp he.continuousAt
  have hRcomp0:R (e 0)=0:=by rw [he0,hR0]
  have hId:(fun w:F=>R (e w)) =ᶠ[𝓝 0] id:=by
    have hrn:=hRcomp.eventually (show injectivityDomain y∈𝓝 (R (e 0)) from by rw [hRcomp0]; exact hn)
    have hri:=he.continuousAt.eventually (show ∀ᶠ v in 𝓝 (e 0),
      riemannianExp y (R v)=riemannianExp x v from by rw [he0]; exact hRi)
    filter_upwards [hei,hrn,hn,hri] with w hw hr hw0 hri
    exact riemannianExp_injOn_injectivityDomain y hr hw0 (hri.trans hw)
  have hCJ:C.comp J=ContinuousLinearMap.id ℝ F:=by
    have H:HasFDerivAt (fun w=>R (e w)) (C.comp J) 0:=
      (show HasFDerivAt R C (e 0) from by rw [he0]; exact hCD).comp 0 hJD
    exact H.fderiv.symm.trans (hId.fderiv_eq.trans (fderiv_id))
  have hsur:Function.Surjective J:=(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((tangent_finrank (n:=n) y).trans (tangent_finrank (n:=n) x).symm)).mp heD
  have hJC:J.comp C=ContinuousLinearMap.id ℝ E:=by
    ext d
    obtain ⟨w,rfl⟩:=hsur d
    have H:=congrArg (fun A:F →L[ℝ] F=>A w) hCJ
    change C (J w)=w at H
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,H]
  have hCI:Function.Injective C:=by
    intro d e h
    have h1:=congrArg (fun A:E →L[ℝ] E=>A d) hJC
    have h2:=congrArg (fun A:E →L[ℝ] E=>A e) hJC
    change J (C d)=d at h1
    change J (C e)=e at h2
    exact h1.symm.trans ((congrArg J h).trans h2)
  exact ⟨e,C,he,he0,hei,hCI,hCJ,hJC,
    expJacobian_eq_normal_endpoint (hR.differentiableAt (by simp)) hR0 hRi⟩
end NormalEndpointInverse
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_InverseProfile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Module
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

lemma symmetric_eigenvalue_pos {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (hn : finrank ℝ E=n) (hpos : ∀ x:E, x≠0 → 0 < inner ℝ (A x) x) (i:Fin n) :
    0 < hA.eigenvalues hn i := by
  have H := hpos (hA.eigenvectorBasis hn i) ((hA.eigenvectorBasis hn).toBasis.ne_zero i)
  rw [hA.apply_eigenvectorBasis,real_inner_smul_left,real_inner_self_eq_norm_sq,
    (hA.eigenvectorBasis hn).norm_eq_one] at H
  simpa using H
end WeakMTWTransport

end



end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_PullbackDet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
open scoped Topology

namespace WeakMTWTransport
section PullbackDet
variable {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace E] [CompleteSpace F]

lemma abs_det_hessian_pullback (B:E →L[ℝ] F) (W:F →L[ℝ] F)
    (hd:Module.finrank ℝ E=Module.finrank ℝ F) :
    |(B.adjoint.comp (W.comp B)).det|=B.toLinearMap.normDet^2*|W.det| := by
  have h1:=LinearMap.normDet_comp_of_finrank_eq B.toLinearMap W.toLinearMap hd
  have h2:=LinearMap.normDet_comp_of_finrank_eq (W.comp B).toLinearMap B.adjoint.toLinearMap hd
  have h3:=LinearMap.normDet_comp_of_finrank_eq B.toLinearMap B.adjoint.toLinearMap hd
  have hs:(B.adjoint.comp B).det=B.toLinearMap.normDet^2:=by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using B.normDet_sq.symm
  rw [LinearMap.normDet_eq_abs_det] at h2 h3
  change |(B.adjoint.comp B).det|=B.adjoint.toLinearMap.normDet*B.toLinearMap.normDet at h3
  rw [hs,abs_of_nonneg (sq_nonneg _)] at h3
  rw [LinearMap.normDet_eq_abs_det] at h1
  change |(B.adjoint.comp (W.comp B)).det|=_ at h2
  rw [h2]
  change B.adjoint.toLinearMap.normDet*(W.comp B).toLinearMap.normDet=_
  rw [show (W.comp B).toLinearMap.normDet=|W.det| *B.toLinearMap.normDet from h1]
  calc
    _ = (B.adjoint.toLinearMap.normDet*B.toLinearMap.normDet)*|W.det| := by ring
    _ = _ := by rw [←h3]

omit [CompleteSpace E] in
lemma symmetric_det_pos {A:E →L[ℝ] E}
    (hA:∀x y,inner ℝ (A x) y=inner ℝ x (A y))
    (hp:∀x,x≠0 → 0 < inner ℝ (A x) x) : 0<A.det := by
  have hs:A.toLinearMap.IsSymmetric:=hA
  change 0<A.toLinearMap.det
  rw [hs.det_eq_prod_eigenvalues rfl]
  exact Finset.prod_pos (fun i _=>symmetric_eigenvalue_pos hs rfl hp i)

lemma det_positive_hessian_pullback {B:E →L[ℝ] F} {W:F →L[ℝ] F}
    (hd:Module.finrank ℝ E=Module.finrank ℝ F) (hi:Function.Injective B)
    (hW:∀x y,inner ℝ (W x) y=inner ℝ x (W y))
    (hp:∀x,x≠0 → 0 < inner ℝ (W x) x) {l:ℝ} (hl:0<l) :
    (∀d,d≠0 → 0 < inner ℝ ((l • (B.adjoint.comp (W.comp B))) d) d) ∧
    (l • (B.adjoint.comp (W.comp B))).det=
      l^Module.finrank ℝ E*B.toLinearMap.normDet^2*W.det := by
  have hs:∀x y,inner ℝ ((l • (B.adjoint.comp (W.comp B))) x) y=
      inner ℝ x ((l • (B.adjoint.comp (W.comp B))) y):=by
    intro x y
    simp only [smul_apply,ContinuousLinearMap.comp_apply,
      real_inner_smul_left,real_inner_smul_right,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right,hW]
  have hpos:∀d,d≠0 → 0 < inner ℝ ((l • (B.adjoint.comp (W.comp B))) d) d := by
    intro d hd
    simp only [smul_apply,ContinuousLinearMap.comp_apply,
      real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left]
    exact mul_pos hl (hp _ (fun h=>hd (hi (h.trans B.map_zero.symm))))
  refine ⟨hpos,?_⟩
  have H:=abs_det_hessian_pullback B W hd
  have hpull:0<(B.adjoint.comp (W.comp B)).det:=by
    apply symmetric_det_pos
    · intro x y
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.adjoint_inner_right,hW]
    · intro d hd
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
      exact hp _ (fun h=>hd (hi (h.trans B.map_zero.symm)))
  rw [abs_of_pos hpull,abs_of_pos (symmetric_det_pos hW hp)] at H
  change (l • (B.adjoint.comp (W.comp B)).toLinearMap).det=_
  rw [LinearMap.det_smul]
  change l^Module.finrank ℝ E*(B.adjoint.comp (W.comp B)).det=_
  rw [H]
  ring
end PullbackDet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_OuterTrueMatrix
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section OuterTrueMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.otFinite
local instance otComplete (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _

lemma WeakMTW.exists_uniform_outer_true_matrix_oai
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0<lam) (hcap:0 ≤ cap) :
    ∃K>0,∀ (x y:M) (p:TangentSpace 𝓘(ℝ,Model n) x)
      (r:TangentSpace 𝓘(ℝ,Model n) y) (G:M×M → ℝ) (l:ℝ),
      riemannianExp x p=y → riemannianExp y r=x → r∈minimizingVectors y →
      Function.Injective (fderiv ℝ (fun v=>extChartAt 𝓘(ℝ,Model n)
        (riemannianExp x p) (riemannianExp x v)) p) →
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G (y,x) →
      (∀ᶠ q in 𝓝 p,G (riemannianExp x q,x)=‖q‖^2/2) →
      (∀ᶠ z in 𝓝 (⟨y,r⟩:TangentBundle 𝓘(ℝ,Model n) M),z.2∈injectivityDomain z.1 →
        (fun q:M×M=>cost q.1 q.2)=ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) → 1<l →
      ∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → StrictMono φ →
      ContDiffAt ℝ 2 φ (uv.2 y) → HasDerivAt φ l (uv.2 y) → iteratedDeriv 2 φ (uv.2 y)≤0 →
      ∀ B:TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ,
      (∀d e,B d e=B e d) → (∀d,0≤B d d) →
      HasLowerSecondTaylor (fun d=>φ (uv.2 (riemannianExp x (p+d)))+‖p+d‖^2/2) 0 B →
      ∃ (C:TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y)
        (V:TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x),
        Function.Injective C ∧ C.toLinearMap.normDet=expJacobian (n:=n) x p ∧
        (∀d,inner ℝ r (C d)=-inner ℝ p d) ∧
        (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
        (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
        (∀d,inner ℝ (V d) d=B d d+(l*hessianValue y (l⁻¹ • r) (C d)-
          fderiv ℝ (fderiv ℝ (fun w=>G (riemannianExp y w,x))) 0 (C d) (C d))-
          (iteratedDeriv 2 φ (uv.2 y)/l^2)*(inner ℝ p d)^2) ∧
        expJacobian (n:=n) y (l⁻¹ • r)*V.det≤l^n*K*(expJacobian (n:=n) x p)^2 := by
  obtain ⟨K,hK,HK⟩:=hmtw.exists_uniform_outer_normal_det_bound_second hlam hcap
  refine ⟨K,hK,?_⟩
  intro x y p r G l hxy hyx hr hp hG hact hagree hl x0 uv φ huv hmono hφ hd hconc B hBs hB hjet
  subst y
  let y:=riemannianExp x p
  let E:=TangentSpace 𝓘(ℝ,Model n) x
  let F:=TangentSpace 𝓘(ℝ,Model n) y
  obtain ⟨e,C,he,he0,hei,hCI,hCJ,hJC,hCd⟩:=exists_normal_endpoint_inverse hp
  let J:F →L[ℝ] E:=fderiv ℝ e 0
  let H:=pullBilinear B J
  have hHs:∀d e,H d e=H e d:=by intro d e; exact hBs (J d) (J e)
  have hHp:∀d,0≤H d d:=fun d=>hB (J d)
  have hJcomp (d:E):J (C d)=d:=congrArg (fun A:E →L[ℝ] E=>A d) hJC
  have hjet2:HasLowerSecondTaylor
      (fun w:F=>φ (uv.2 (riemannianExp y w))+G (riemannianExp y w,x)) 0 H:=by
    have ha:HasFDerivAt (fun w:F=>e w-p) J 0:=
      (he.differentiableAt (by simp)).hasFDerivAt.sub_const p
    have Z:=HasLowerSecondTaylor.comp_stationary hjet ha (by rw [he0,sub_self])
    have ha':=he.continuousAt.eventually (show ∀ᶠ q in 𝓝 (e 0),G (riemannianExp x q,x)=‖q‖^2/2
      from by rw [he0]; exact hact)
    have hEq:(fun w:F=>φ (uv.2 (riemannianExp x (p+(e w-p))))+‖p+(e w-p)‖^2/2) =ᶠ[𝓝 0]
        (fun w:F=>φ (uv.2 (riemannianExp y w))+G (riemannianExp y w,x)):=by
      filter_upwards [hei,ha'] with w hw ha
      have hh:p+(e w-p)=e w:=by abel
      rw [hh,←hw,ha]
    exact Z.mono hEq.eq_of_nhds hEq.le
  have hG':ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (y,riemannianExp y r):=by rw [hyx]; exact hG
  obtain ⟨N,hNs,hNp,hNd,hNdet⟩:=HK y r G l hr hG' hagree hl x0 uv φ huv hmono hφ hd hconc H hHs hHp
    (by simpa only [y,hyx] using hjet2)
  have hcD:HasFDerivAt (fun w:F=>G (riemannianExp y w,x)) (innerSL ℝ (-r)) 0:=by
    have HH:=cost_branch_normal_jets (r:=r) (T:=(1:ℝ)) (by norm_num)
      (by simpa only [one_smul] using hG') (by simpa only [one_smul] using hagree)
      (fun s hs=>contracted_minimizer_mem_injectivityDomain hr hs.1 hs.2)
    simpa only [one_smul,hyx] using HH.2.1
  have heq:(fun w:F=>G (riemannianExp y w,x)) =ᶠ[𝓝 0] (fun w:F=>‖e w‖^2/2):=by
    have ha':=he.continuousAt.eventually (show ∀ᶠ q in 𝓝 (e 0),G (riemannianExp x q,x)=‖q‖^2/2
      from by rw [he0]; exact hact)
    filter_upwards [hei,ha'] with w hw ha
    rw [←hw,ha]
  have henergy:HasFDerivAt (fun v:E=>‖v‖^2/2) (innerSL ℝ p) p:=by
    convert! ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_mul (1/2:ℝ)) using 1
    · ext v; ring
    · ext v; simp only [smul_apply,smul_eq_mul] <;> ring
  have henergy2:HasFDerivAt (fun w:F=>‖e w‖^2/2) ((innerSL ℝ p).comp J) 0:=
    (show HasFDerivAt (fun v:E=>‖v‖^2/2) (innerSL ℝ p) (e 0) from by rw [he0]; exact henergy).comp
      0 (he.differentiableAt (by simp)).hasFDerivAt
  have hpair:∀d,inner ℝ r (C d)=-inner ℝ p d:=by
    intro d
    have HH:innerSL ℝ (-r)=(innerSL ℝ p).comp J:=
      (hcD.congr_of_eventuallyEq heq.symm).unique henergy2
    have hh:=congrArg (fun A:F →L[ℝ] ℝ=>A (C d)) HH
    simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,inner_neg_left,hJcomp] at hh
    linarith only [hh]
  let V:=C.adjoint.comp (N.comp C)
  have hVs:∀d e,inner ℝ (V d) e=inner ℝ d (V e):=by
    intro d e
    simp only [V,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right,hNs]
  have hpos:=det_positive_hessian_pullback (B:=C) (W:=N)
    ((tangent_finrank x).trans (tangent_finrank y).symm) hCI hNs hNp (l:=1) (by norm_num)
  simp only [one_smul,one_pow,one_mul] at hpos
  refine ⟨C,V,hCI,hCd.symm,hpair,hVs,hpos.1,?_,?_⟩
  · intro d
    simp only [V,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
    rw [hNd,hyx]
    change B (J (C d)) (J (C d))+_ -_ =_
    rw [hJcomp,hpair,neg_sq]
  · have HV:V.det=expJacobian (n:=n) x p^2*N.det:=by rw [hpos.2,←hCd]
    rw [HV]
    nlinarith only [mul_le_mul_of_nonneg_right hNdet (sq_nonneg (expJacobian (n:=n) x p))]
end OuterTrueMatrix
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_true_matrix_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_true_matrix_oai.{u_1}
