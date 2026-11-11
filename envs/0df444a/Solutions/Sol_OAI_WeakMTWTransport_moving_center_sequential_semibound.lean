-- Prove2me | solution 1 for OAI.WeakMTWTransport.moving_center_sequential_semibound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:18:51.768821+00:00
-- url     : https://prove2.me/submissions/6e27c288-73dc-4b3d-937f-a013601fb210

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
import Theorems.Thm_OAI_WeakMTWTransport_parametric_short_pullback_semibound

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ShortEnvelopeJetTest
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma secondJetPullback_apply (j : F →L[ℝ] ℝ) (h : F →L[ℝ] F →L[ℝ] ℝ)
    (m : E →L[ℝ] F) (r : E →L[ℝ] E →L[ℝ] F) (v w : E) :
    secondJetPullback j h m r v w=h (m v) (m w)+j (r v w) := rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_StationaryPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MovingPrefix
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

lemma movingPrefix_contMDiffAt {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (Function.uncurry (movingPrefix a t)) (b,p) := by
  exact (movingNormal_contMDiffAt (q := (b,t • p)) hb).comp (b,p)
    (contDiffAt_fst.prodMk (contDiffAt_snd.const_smul t)).contMDiffAt

lemma movingPrefixEnergy_axis_near {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    (movingPrefixEnergy a t b)=ᶠ[𝓝 p]
      (fun q=>t*(‖(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) q‖^2/2)) := by
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
    ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  filter_upwards [(L.continuous.tendsto p).eventually (prefixAction_axis_near hp)] with q hq
  simpa only [movingPrefixEnergy,movingNormal_zero hb,movingPrefix_eq hb,
    prefixAction,riemannianExp_zero] using hq

lemma movingPrefixEnergy_hessian {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) (d e : Model n) :
    fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p d e=
      t*inner ℝ
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) d)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) e) := by
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
    ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  rw [((movingPrefixEnergy_axis_near hb hp).fderiv (𝕜 := ℝ)).fderiv_eq]
  rw [second_fderiv_const_mul]
  have H := second_fderiv_comp_affine (f := fun q=>‖q‖^2/2) L 0 p
    ((half_norm_sq_contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt) d e
  simpa only [zero_add,half_norm_sq_second_fderiv,innerSL_apply_apply,smul_apply,
    smul_eq_mul] using congrArg (fun r:ℝ=>t*r) H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinatePole
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
lemma movingPrefix_chart_pullback {a c : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source) (f : M → ℝ) :
    (fun q=>f ((extChartAt 𝓘(ℝ,Model n) c).symm (movingPrefixChart a c t b q)))=ᶠ[𝓝 p]
      (fun q=>f (movingPrefix a t b q)) := by
  have hN : ContinuousAt (movingPrefix a t b) p :=
    ((movingPrefix_contMDiffAt (p := p) hb).continuousAt).comp
      (show ContinuousAt (fun q:Model n=>(b,q)) p from by fun_prop)
  filter_upwards [hN.eventually ((isOpen_extChartAt_source (I := 𝓘(ℝ,Model n)) c).mem_nhds hc)]
    with q hq
  exact congrArg f ((extChartAt 𝓘(ℝ,Model n) c).left_inv hq)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinateMatrices
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
lemma coordinateCenterMatrix_chart {a c : M} {t : ℝ} {G : M → ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    coordinateCenterMatrix a t G b p=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p+
      fderiv ℝ (fderiv ℝ (fun q=>G
        ((extChartAt 𝓘(ℝ,Model n) c).symm (movingPrefixChart a c t b q)))) p := by
  exact congrArg (fun B=>fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p+B)
    (((movingPrefix_chart_pullback hb hc _).fderiv (𝕜 := ℝ)).fderiv_eq.symm)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActiveGraphLimit
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

lemma chartFiberInverse_at_center (a : M) (p : Model n) :
    chartFiberInverse a ((extChartAt 𝓘(ℝ,Model n) a) a) p=p := by
  dsimp only [chartFiberInverse]
  rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)]
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) a)]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source a)
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_JointMovingPrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section JointMovingPrefix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma joint_movingPrefix_contMDiffAt {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,(ℝ×Model n)×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : (ℝ×Model n)×Model n=>movingPrefix a q.1.1 q.1.2 q.2) ((t,b),p) := by
  exact (movingNormal_contMDiffAt (q := (b,t • p)) hb).comp ((t,b),p)
    (contDiffAt_fst.snd.prodMk (contDiffAt_fst.fst.smul contDiffAt_snd)).contMDiffAt

lemma joint_movingPrefixChart_contDiffAt {a c : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    ContDiffAt ℝ ∞
      (fun q : (ℝ×Model n)×Model n=>movingPrefixChart a c q.1.1 q.1.2 q.2) ((t,b),p) := by
  exact ((contMDiffAt_extChartAt' (I := 𝓘(ℝ,Model n))
    (by simpa only [extChartAt_source] using hc)).comp ((t,b),p)
      (joint_movingPrefix_contMDiffAt hb)).contDiffAt

lemma joint_movingPrefixEnergy_contDiffAt {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (ht : t≠0)
    (hp : t • chartFiberInverse a b p∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    ContDiffAt ℝ ∞
      (fun q : (ℝ×Model n)×Model n=>movingPrefixEnergy a q.1.1 q.1.2 q.2) ((t,b),p) := by
  have hA : ContMDiffAt 𝓘(ℝ,(ℝ×Model n)×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : (ℝ×Model n)×Model n=>movingNormal a (q.1.2,0)) ((t,b),p) :=
    (movingNormal_contMDiffAt (q := (b,0)) hb).comp ((t,b),p)
      (contDiffAt_fst.snd.prodMk contDiffAt_const).contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm b,t • chartFiberInverse a b p⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hp
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q:M×M=>cost q.1 q.2) (movingNormal a (b,0),movingPrefix a t b p) := by
    simpa only [movingNormal_zero hb,movingPrefix_eq hb,chartFiberInverse] using hC
  exact ((hC'.comp ((t,b),p) (hA.prodMk (joint_movingPrefix_contMDiffAt hb))).contDiffAt.div
    contDiffAt_fst.fst ht)

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma movingPrefix_at_center (a : M) (t : ℝ) (p : Model n) :
    movingPrefix a t (extChartAt 𝓘(ℝ,Model n) a a) p=riemannianExp a (t • p) := by
  have hb := (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  rw [movingPrefix_eq hb]
  change riemannianExp _ (t • chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a) p)=_
  rw [chartFiberInverse_at_center,(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)]
  rfl

lemma movingPrefixEnergy_hessian_at_center {a : M} {p : Model n}
    (hp : p∈injectivityDomain a) (d e : Model n) :
    fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 (extChartAt 𝓘(ℝ,Model n) a a))) p d e=
      inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from d) e := by
  have hb := (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hbase := (extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)
  have hL (r : Model n) :
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ a r=r := by
    rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) a)]
    exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source a)
  have hp' : (1:ℝ) • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)) p∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)) := by
    rw [hbase]
    simp only [hL]
    change (1:ℝ) • (show TangentSpace 𝓘(ℝ,Model n) a from p)∈injectivityDomain a
    rw [one_smul]
    exact hp
  have H := movingPrefixEnergy_hessian hb hp' d e
  rw [hbase] at H
  simpa only [hL,one_mul] using H

end JointMovingPrefix
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_MovingCenterSemibound
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MovingCenterSemibound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [Nonempty M] in
lemma moving_energy_hessian_tendsto {a : M} {q : Model n}
    (hq : (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a) {bj qj : ℕ → Model n} {tj : ℕ → ℝ}
    (hb : Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq : Tendsto qj atTop (𝓝 q)) (ht : Tendsto tj atTop (𝓝 1))
    : Tendsto (fun i=>fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i)) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 (extChartAt 𝓘(ℝ,Model n) a a))) q)) := by
  let b := extChartAt 𝓘(ℝ,Model n) a a
  have hb0 : b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hp0 : (1:ℝ) • chartFiberInverse a b q∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) := by
    rw [chartFiberInverse_at_center]
    rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)]
    change (1:ℝ) • (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a
    rw [one_smul]
    exact hq
  let f : (ℝ×Model n) → Model n → ℝ := fun z r=>movingPrefixEnergy a z.1 z.2 r
  have henergy : ContDiffAt ℝ ∞ (Function.uncurry f) ((1,b),q) :=
    joint_movingPrefixEnergy_contDiffAt hb0 one_ne_zero hp0
  have hd : ContDiffAt ℝ ∞ (fun z:(ℝ×Model n)×Model n=>fderiv ℝ (fderiv ℝ (f z.1)) z.2) ((1,b),q) :=
    ContDiffAt.partial_snd_fderiv_two (f := f) (q := (1,b)) (h := q) henergy
  have harg : Tendsto (fun i=>((tj i,bj i),qj i)) atTop (𝓝 ((1,b),q)) :=
    (ht.prodMk_nhds hb).prodMk_nhds hqq
  have H := hd.continuousAt.tendsto.comp harg
  exact H

omit [Nonempty M] in
lemma moving_energy_sequential_lower {a : M} {q : Model n}
    (hq : (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a) {bj qj : ℕ → Model n} {tj : ℕ → ℝ}
    (hb : Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq : Tendsto qj atTop (𝓝 q)) (ht : Tendsto tj atTop (𝓝 1))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ i in atTop,∀ d : Model n,
      inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from d) d-ε*‖d‖^2≤
        fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i) d d := by
  let b := extChartAt 𝓘(ℝ,Model n) a a
  have hElim := moving_energy_hessian_tendsto hq hb hqq ht
  have hEsmall := ((Metric.tendsto_nhds (α := Model n →L[ℝ] Model n →L[ℝ] ℝ)).mp hElim) ε hε
  filter_upwards [hEsmall] with i hei
  intro d
  have HE := (abs_le.mp (bilinear_diag_sub_bound
    (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i))
    (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 b)) q) d)).1
  rw [movingPrefixEnergy_hessian_at_center hq] at HE
  have hei' : ‖(fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i))-
    (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 b)) q)‖<ε := by
    exact (dist_eq_norm (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i))
      (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 b)) q)).symm ▸ hei
  have HM := mul_le_mul_of_nonneg_right hei'.le (sq_nonneg ‖d‖)
  linarith only [HE,HM]

omit [Nonempty M] [CompleteSpace P] in
lemma moving_chart_support_jet {a c : M} {ψ : P×Model n → ℝ} {p : P} {x q : Model n}
    (hψ : ContDiffAt ℝ ∞ ψ (p,x))
    (he : extChartAt 𝓘(ℝ,Model n) c (riemannianExp a q)=x)
    (hc : riemannianExp a q∈(extChartAt 𝓘(ℝ,Model n) c).source) (d : Model n) :
    let g := movingPrefixChart a c 1 (extChartAt 𝓘(ℝ,Model n) a a)
    secondJetPullback (fderiv ℝ (fun w=>ψ (p,w)) x)
      (fderiv ℝ (fderiv ℝ (fun w=>ψ (p,w))) x)
      (fderiv ℝ g q) (fderiv ℝ (fderiv ℝ g) q) d d=
      fderiv ℝ (fderiv ℝ (fun r=>ψ (p,extChartAt 𝓘(ℝ,Model n) c (riemannianExp a r)))) q d d := by
  let b := extChartAt 𝓘(ℝ,Model n) a a
  let g := movingPrefixChart a c 1 b
  have hb0 : b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hgc : movingPrefix a 1 b q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    simpa only [b,movingPrefix_at_center,one_smul] using hc
  have hg : ContDiffAt ℝ ∞ (fun z:(ℝ×Model n)×Model n=>movingPrefixChart a c z.1.1 z.1.2 z.2) ((1,b),q) :=
    joint_movingPrefixChart_contDiffAt hb0 hgc
  have hgb : ContDiffAt ℝ 2 g q :=
    (hg.comp q (contDiffAt_const.prodMk contDiffAt_id)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hge : g q=x := by
    simpa only [g,movingPrefixChart,b,movingPrefix_at_center,one_smul] using he
  have hψb : ContDiffAt ℝ 2 (fun w=>ψ (p,w)) (g q) := by
    rw [hge]
    exact (hψ.comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  change secondJetPullback _ _ (fderiv ℝ g q) (fderiv ℝ (fderiv ℝ g) q) d d=_
  rw [←hge,secondJetPullback_apply,←second_fderiv_comp_with_acceleration hψb hgb]
  have hgfun : g=(fun r : Model n=>extChartAt 𝓘(ℝ,Model n) c (riemannianExp a r)) := by
    funext r
    simp only [g,movingPrefixChart,b,movingPrefix_at_center,one_smul]
  rw [hgfun]
  rfl

lemma moving_center_sequential_semibound_oai {a c : M} {ψ : P×Model n → ℝ}
    {p : P} {x q : Model n} (L : ℝ≥0)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) c).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x))
    (hq : (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a) (he : extChartAt 𝓘(ℝ,Model n) c (riemannianExp a q)=x)
    (hc : riemannianExp a q∈(extChartAt 𝓘(ℝ,Model n) c).source)
    {pj : ℕ → P} {xj bj qj : ℕ → Model n} {tj τj : ℕ → ℝ} {f : ℕ → M → ℝ}
    (hp : Tendsto pj atTop (𝓝 p)) (hxx : Tendsto xj atTop (𝓝 x))
    (hb : Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq : Tendsto qj atTop (𝓝 q)) (ht : Tendsto tj atTop (𝓝 1))
    (hτ : Tendsto τj atTop (𝓝 0)) (hτpos : ∀ᶠ i in atTop,0<τj i)
    (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
    (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
    (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) c).symm (xj i))=ψ (pj i,xj i))
    (hz : ∀ᶠ i in atTop,movingPrefixChart a c (tj i) (bj i) (qj i)=
      parametricShortForward c ψ ((pj i,τj i),xj i))
    (hjet : ∀ᶠ i in atTop,
      (∀ᶠ z in 𝓝 (movingPrefixChart a c (tj i) (bj i) (qj i)),DifferentiableAt ℝ
        (fun z=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm z)) z) ∧
      DifferentiableAt ℝ (fderiv ℝ
        (fun z=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm z)))
          (movingPrefixChart a c (tj i) (bj i) (qj i)))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ i in atTop,∀ d : Model n,
      inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from d) d+
        fderiv ℝ (fderiv ℝ (fun r=>ψ (p,extChartAt 𝓘(ℝ,Model n) c (riemannianExp a r)))) q d d-
          ε*‖d‖^2 ≤ coordinateCenterMatrix a (tj i) (hopfLax (τj i) (f i)) (bj i) (qj i) d d := by
  let b := extChartAt 𝓘(ℝ,Model n) a a
  let g := fun (t:ℝ×Model n) (r:Model n)=>movingPrefixChart a c t.1 t.2 r
  have hb0 : b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hgc : movingPrefix a 1 b q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    simpa only [b,movingPrefix_at_center,one_smul] using hc
  have hg : ContDiffAt ℝ ∞ (Function.uncurry g) ((1,b),q) :=
    joint_movingPrefixChart_contDiffAt hb0 hgc
  have harg := (ht.prodMk_nhds hb).prodMk_nhds hqq
  have hm := (ContDiffAt.partial_snd_fderiv hg).continuousAt.tendsto.comp harg
  have hr := (ContDiffAt.partial_snd_fderiv_two hg).continuousAt.tendsto.comp harg
  have hgj : ∀ᶠ i in atTop,ContDiffAt ℝ 2 (g (tj i,bj i)) (qj i) := by
    have hg2 := hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    filter_upwards [harg.eventually (hg2.eventually (by norm_num))] with i hi
    exact hi.comp (qj i) (contDiffAt_const.prodMk contDiffAt_id)
  have H := parametric_short_pullback_semibound L hx hψ hp hxx hτ hτpos hlip hbelow htouch
    hz ((hjet.and hgj).mono (fun i hi=>⟨hi.1.1,hi.1.2,hi.2⟩)) hm hr (half_pos hε)
  have HE := moving_energy_sequential_lower hq hb hqq ht (half_pos hε)
  have hpull := moving_chart_support_jet hψ he hc
  have hbjt := hb.eventually ((isOpen_extChartAt_target a).mem_nhds hb0)
  have hcjt : ∀ᶠ i in atTop,movingPrefix a (tj i) (bj i) (qj i)∈(extChartAt 𝓘(ℝ,Model n) c).source :=
    ((joint_movingPrefix_contMDiffAt hb0).continuousAt.tendsto.comp harg).eventually
      ((isOpen_extChartAt_source _).mem_nhds hgc)
  filter_upwards [H,HE,hbjt,hcjt] with i hi hei hbi hci
  intro d
  have HD := hi d
  rw [hpull d] at HD
  have HD2 := hei d
  rw [coordinateCenterMatrix_chart hbi hci,add_apply,add_apply]
  linarith only [HD,HD2]

end MovingCenterSemibound
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.WeakMTWTransport.moving_center_sequential_semibound_oai.{u_1, u_2} := @OAI.WeakMTWTransport.moving_center_sequential_semibound_oai.{u_1, u_2}
