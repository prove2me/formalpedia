-- Prove2me | solution 1 for OAI.WeakMTWTransport.MaximumJensenFamily.eventual_outward
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:41:14.877749+00:00
-- url     : https://prove2.me/submissions/c630bcd4-21e1-43f8-8043-56f4883932f7

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
-- module Solutions.OAIQ232_BH.Compat
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MetricDefinitions
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

variable {M : Type*} [MetricSpace M]

variable [CompactSpace M] [Nonempty M]

lemma dualPair_contact_left {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) : ∃ y, contactGap u v x y = 0 := by
  rw [huv.1]
  exact cTransform_gap_zero hv x

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_CompactDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma cTransform_add_const {v : M → ℝ} (hv : Continuous v) (a : ℝ) :
    cTransform (fun x => v x + a) = fun x => cTransform v x - a := by
  funext x
  apply le_antisymm
  · rw [cTransform_le_iff (v := fun x => v x + a) (hv.add continuous_const)]
    intro y
    have hh := ((cTransform_le_iff hv x (cTransform v x)).mp le_rfl) y
    linarith
  · obtain ⟨y, hy, _⟩ := exists_cTransform_contact hv x
    have hh := cTransform_gap_nonneg (v := fun x => v x + a) (hv.add continuous_const) x y
    dsimp [contactGap] at hh
    linarith

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_GlobalSupport
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

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.active_hull_global_support
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x)) :
    p ∈ minimizingVectors x ∧ ∀ a : M,
      cTransform v x+cost x (riemannianExp x p) ≤
        cTransform v a+cost a (riemannianExp x p) :=
  hmtw.global_support hv (active_hull_subset_normalSubdifferential hv x hp)

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

lemma movingPrefixEnergy_contDiffAt {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingPrefixEnergy a t)) (b,p) := by
  have hA : ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (fun q:Model n×Model n=> movingNormal a (q.1,0)) (b,p) :=
    (movingNormal_contMDiffAt (q := (b,0)) hb).comp (b,p)
      (contDiffAt_fst.prodMk contDiffAt_const).contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm b,
      t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q:M×M=>cost q.1 q.2) (movingNormal a (b,0),movingPrefix a t b p) := by
    simpa only [movingNormal_zero hb,movingPrefix_eq hb] using hC
  exact ((hC'.comp (b,p) (hA.prodMk (movingPrefix_contMDiffAt hb))).contDiffAt.div_const t)

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_GraphCoordinates
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
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] in
lemma graph_coordinates_at_center (q : TangentBundle 𝓘(ℝ,Model n) M) :
    graphVelocityCoordinate q.1 q=q.2 := by
  unfold graphVelocityCoordinate
  rw [tangent_chart_apply]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source q.1)
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActiveLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma positive_barycentric_restriction {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (p : ι → E) (w : ι → ℝ)
    (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) :
    let κ := {i : ι // 0<w i}
    Nonempty κ ∧ (∑ i:κ,w i=1) ∧
      (∑ i:κ,w i • p i=∑ i,w i • p i) ∧
      ∀ f : ι → ℝ,∑ i:κ,w i*f i=∑ i,w i*f i := by
  classical
  dsimp only
  have he (f : ι → E) : (∑ i:{i : ι // 0<w i},w i • f i)=∑ i,w i • f i := by
    rw [←Finset.sum_subtype (p := fun i=>0<w i) (Finset.univ.filter (fun i=>0<w i)) (by simp) (fun i=>w i • f i)]
    exact Finset.sum_subset (Finset.filter_subset _ _) (by
      intro i hi hn
      have hi0 : w i=0 := le_antisymm (not_lt.mp (by simpa using hn)) (hw i)
      simp only [hi0,zero_smul])
  have hr (f : ι → ℝ) : (∑ i:{i : ι // 0<w i},w i*f i)=∑ i,w i*f i := by
    rw [←Finset.sum_subtype (p := fun i=>0<w i) (Finset.univ.filter (fun i=>0<w i)) (by simp) (fun i=>w i*f i)]
    exact Finset.sum_subset (Finset.filter_subset _ _) (by
      intro i hi hn
      have hi0 : w i=0 := le_antisymm (not_lt.mp (by simpa using hn)) (hw i)
      simp only [hi0,zero_mul])
  have hsum : (∑ i:{i : ι // 0<w i},w i)=1 := by
    simpa only [mul_one] using (hr (fun _=>1)).trans (by simpa only [mul_one] using hs)
  refine ⟨?_,hsum,he p,hr⟩
  by_contra hn
  have : IsEmpty {i : ι // 0<w i} := not_nonempty_iff.mp hn
  simp at hsum

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MovingHessianLimit
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
variable {Q E F : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma tendsto_clm_apply {ι : Type*} {l : Filter ι}
    {A : ι → E →L[ℝ] F} {v : ι → E} {A₀ : E →L[ℝ] F} {v₀ : E}
    (hA : Tendsto A l (𝓝 A₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i=>A i (v i)) l (𝓝 (A₀ v₀)) := by
  have hc : Continuous (fun q:(E →L[ℝ] F)×E => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  exact (hc.tendsto (A₀,v₀)).comp (hA.prodMk_nhds hv)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartParameter
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
section ChartParameter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma MaximumRow.parameter_nonnegative {v : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {z : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    {ι : Type} [Fintype ι] (pj : ι → TangentSpace 𝓘(ℝ,Model n) R.q.1.1) (w : ι → ℝ)
    (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) (hb : ∑ i,w i • pj i=R.q.1.2)
    (ha : ∀ i,pj i∈activeLogs (modifiedDatum v α D b Bo) R.q.1.1) :
    1/4096+4*b/bplus≤Bc ((v (riemannianExp R.q.1.1 R.q.1.2)-α)/D)-
      ∑ i,w i*Bo ((v (riemannianExp R.q.1.1 (pj i))-α)/D) := by
  classical
  let κ := {i : ι // 0<w i}
  have H := positive_barycentric_restriction pj w hw hs
  let : Nonempty κ := H.1
  have HP := R.parameter κ (fun i=>pj i) (fun i=>w i) (fun i=>i.2)
    H.2.1 (H.2.2.1.trans hb) (fun i=>ha i)
  rw [H.2.2.2 (fun i=>Bo ((v (riemannianExp R.q.1.1 (pj i))-α)/D))] at HP
  exact HP

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma MaximumRow.chart_first_limit_parameter {v G : M → ℝ} {α D b bplus t : ℝ}
    {Bc Bo : ℝ → ℝ} {a z : M} (R : MaximumRow (n := n) v α D b bplus t Bc Bo z)
    (ha : R.q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source)
    {q : ℕ → subgradientGraph (n := n) (cTransform (modifiedDatum v α D b Bo))}
    (J : ChartFixedPrefixLimit a (modifiedDatum v α D b Bo) G t q R.q) :
    let x := graphBaseCoordinate a R.q.1
    1/4096+4*b/bplus≤Bc ((v (movingNormal a (x,graphVelocityCoordinate a R.q.1))-α)/D)-
      ∑ i,J.w₀ i*Bo ((v (movingNormal a (x,J.pj₀ i))-α)/D) := by
  let x := graphBaseCoordinate a R.q.1
  let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ R.q.1.1
  have hre := graph_coordinate_reconstruction ha
  have hbase : (extChartAt 𝓘(ℝ,Model n) a).symm x=R.q.1.1 :=
    congrArg Bundle.TotalSpace.proj hre
  have hvel : A (graphVelocityCoordinate a R.q.1)=R.q.1.2 := by
    have H := congrArg (fun w:TangentBundle 𝓘(ℝ,Model n) M=>show Model n from w.2) hre
    change chartFiberInverse a x (graphVelocityCoordinate a R.q.1)=R.q.1.2 at H
    unfold chartFiberInverse at H
    rw [hbase] at H
    exact H
  let pj : Fin (Module.finrank ℝ (Model n)+1) → TangentSpace 𝓘(ℝ,Model n) R.q.1.1 :=
    fun i=>A (J.pj₀ i)
  have hbar : ∑ i,J.w₀ i • pj i=R.q.1.2 := by
    calc
      _=A (∑ i,J.w₀ i • J.pj₀ i) := by simp [pj]
      _=R.q.1.2 := by rw [J.baryLimit]; exact hvel
  have hactive : ∀ i,pj i∈activeLogs (modifiedDatum v α D b Bo) R.q.1.1 := by
    intro i
    have HH := J.activeLimit i
    change chartFiberInverse a x (J.pj₀ i)∈activeLogs _ ((extChartAt 𝓘(ℝ,Model n) a).symm x) at HH
    unfold chartFiberInverse at HH
    rw [hbase] at HH
    exact HH
  have HP := R.parameter_nonnegative pj J.w₀ J.nonnegLimit J.totalLimit hbar hactive
  have hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target := (extChartAt 𝓘(ℝ,Model n) a).map_source ha
  have he (p : Model n) : movingNormal a (x,p)=riemannianExp R.q.1.1 (A p) := by
    rw [movingNormal_eq hx,hbase]
  change 1/4096+4*b/bplus≤Bc ((v (movingNormal a (x,graphVelocityCoordinate a R.q.1))-α)/D)-
      ∑ i,J.w₀ i*Bo ((v (movingNormal a (x,J.pj₀ i))-α)/D)
  simp only [he,hvel]
  exact HP

end ChartParameter
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearClose
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

lemma bilinear_quadratic_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E →L[ℝ] ℝ) (d:E) : |A d d|≤‖A‖*‖d‖^2 := by
  calc
    |A d d| = ‖A d d‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖A d‖*‖d‖ := (A d).le_opNorm d
    _ ≤ (‖A‖*‖d‖)*‖d‖ := mul_le_mul_of_nonneg_right (A.le_opNorm d) (norm_nonneg d)
    _ = ‖A‖*‖d‖^2 := by ring

lemma bilinear_quadratic_close {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E →L[ℝ] E →L[ℝ] ℝ} {ε:ℝ} (h : ‖A-B‖≤ε) (d:E) :
    A d d≤B d d+ε*‖d‖^2 := by
  have H := (le_abs_self ((A-B) d d)).trans (bilinear_quadratic_norm_bound (A-B) d)
  have HH := H.trans (mul_le_mul_of_nonneg_right h (sq_nonneg ‖d‖))
  simpa only [_root_.sub_apply,sub_le_iff_le_add,add_comm] using HH

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearAbsorption
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section BilinearAbsorption
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma covectorSquare_apply (p:E →L[ℝ] ℝ) (d e:E) : covectorSquare p d e=p d*p e := rfl

attribute [local instance] OAI.WeakMTWTransport.bilinearAbsorptionDualNormedAddCommGroup
attribute [local instance] OAI.WeakMTWTransport.bilinearAbsorptionDualNormedSpace
local instance bilinearAbsorptionBilinearNormedAddCommGroup_rf85feb_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance bilinearAbsorptionBilinearNormedSpace_rf85feb_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
lemma covectorSquare_continuous : Continuous (covectorSquare (E := E)) := by
  exact isBoundedBilinearMap_smulRight.continuous.comp (continuous_id.prodMk continuous_id)

lemma eventual_moving_rank_lower {ι:Type*} {l:Filter ι}
    {G R H:ι → E →L[ℝ] E →L[ℝ] ℝ} {G₀ R₀:E →L[ℝ] E →L[ℝ] ℝ}
    {A C δ:ℝ} (hA:0<A) (hδ:0<δ) (hG₀:∀d:E,δ*‖d‖^2≤G₀ d d)
    (hG:Tendsto G l (𝓝 G₀)) (hR:Tendsto R l (𝓝 R₀))
    (hH:∀ ε:ℝ,0<ε → ∀ᶠ k in l,∀d:E,
      A*G₀ d d+C*R₀ d d-ε*‖d‖^2≤H k d d) :
    ∀ᶠ k in l,∀d:E,A/2*G k d d+C*R k d d≤H k d d := by
  let ε := A*δ/4
  have he:0<ε := by dsimp [ε] <;> positivity
  have hlim : Tendsto (fun k=>(A/2) • G k+C • R k) l (𝓝 ((A/2) • G₀+C • R₀)) :=
    (hG.const_smul _).add (hR.const_smul _)
  have hn : ∀ᶠ k in l,‖((A/2) • G k+C • R k)-((A/2) • G₀+C • R₀)‖≤ε := by
    have ht := (hlim.sub_const ((A/2) • G₀+C • R₀)).norm
    simp only [sub_self,norm_zero] at ht
    exact (ht.eventually (gt_mem_nhds he)).mono (fun _ h=>h.le)
  filter_upwards [hn,hH ε he] with k hk hhk
  intro d
  have hb := bilinear_quadratic_close hk d
  simp only [add_apply,smul_apply,smul_eq_mul] at hb
  have hpos := mul_le_mul_of_nonneg_left (hG₀ d) (show 0≤A/2 by positivity)
  dsimp only [ε] at hb hhk
  nlinarith only [hb,hhk d,hpos]

end BilinearAbsorption
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OutwardWeightCap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport

lemma outward_weight_and_cap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ℕ} (hN : Fintype.card ι≤N) {m d B : ι → ℝ} {q D c : ℝ}
    (hm : ∀ i,0 < m i) (hsum : ∑ i,m i=1) (hbar : ∑ i,m i*d i=0)
    (hq : 0<q) (hD : 0<D) (hc : 0 < c) (right : Finset ι)
    (hrmass : c≤∑ i∈right,m i)
    (hr : ∀ i∈right,2*q*d i+d i^2≤-D/4)
    (ho : ∀ i,0<d i → 2*q*d i+d i^2≤3*D)
    (hB : ∀ i,0≤B i) (hcap : ∑ i,m i*B i≤1) :
    ∃ i, 0<d i ∧ c/(12*(N:ℝ))≤ m i ∧ c*D/(8*(N:ℝ)*q)≤ m i*d i ∧
      d i≤3*D/(2*q) ∧ B i≤12*(N:ℝ)/c := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra H
    have : (Finset.univ : Finset ι)=∅ := Finset.not_nonempty_iff_eq_empty.mp H
    rw [this,Finset.sum_empty] at hsum
    norm_num at hsum
  have hNp : 0<(N:ℝ) := by
    have : 0<Fintype.card ι := by simpa only [Finset.card_univ] using Finset.card_pos.mpr hne
    exact_mod_cast this.trans_le hN
  have hrneg : ∀ i∈right,d i<0 ∧ D/(8*q)≤-d i := by
    intro i hi
    have H := hr i hi
    constructor
    · by_contra hn
      have hdi : 0≤d i := le_of_not_gt hn
      nlinarith only [H,mul_nonneg hq.le hdi,sq_nonneg (d i),hD]
    · apply (div_le_iff₀ (by positivity : 0<8*q)).mpr
      nlinarith only [H,sq_nonneg (d i)]
  have hmoment : c*D/(8*q)≤∑ i,m i*max (d i) 0 := by
    have he : (∑ i,m i*max (d i) 0)=(∑ i,m i*max (-d i) 0) := by
      have HH : ∀ i,m i*d i=m i*max (d i) 0-m i*max (-d i) 0 := by
        intro i
        by_cases hd : 0≤d i
        · rw [max_eq_left hd,max_eq_right (neg_nonpos.mpr hd)]; ring
        · have hd' : d i≤0 := le_of_not_ge hd
          rw [max_eq_right hd',max_eq_left (neg_nonneg.mpr hd')]; ring
      simp_rw [HH] at hbar
      rw [Finset.sum_sub_distrib] at hbar
      linarith
    rw [he]
    calc
      c*D/(8*q)≤(∑ i∈right,m i)*(D/(8*q)) := by
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hrmass (by positivity : 0≤D/(8*q))
      _=∑ i∈right,m i*(D/(8*q)) := by rw [Finset.sum_mul]
      _≤∑ i∈right,m i*max (-d i) 0 := Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left ((hrneg i hi).2.trans (le_max_left _ _)) (hm i).le)
      _≤∑ i,m i*max (-d i) 0 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ right) (fun i _ _ => mul_nonneg (hm i).le (le_max_right _ _))
  let a : ℝ := c*D/(8*(N:ℝ)*q)
  have ha : 0<a := by dsimp [a] <;> positivity
  have hsum_a : (∑ _i : ι,a)≤∑ i,m i*max (d i) 0 := by
    calc
      _=(Fintype.card ι:ℝ)*a := by simp
      _≤(N:ℝ)*a := mul_le_mul_of_nonneg_right (by exact_mod_cast hN) ha.le
      _=c*D/(8*q) := by dsimp [a]; field_simp
      _≤_ := hmoment
  obtain ⟨i,_,hi⟩ := Finset.exists_le_of_sum_le hne hsum_a
  have hdi : 0<d i := by
    by_contra H
    rw [max_eq_right (le_of_not_gt H),mul_zero] at hi
    exact (not_le_of_gt ha) hi
  rw [max_eq_left hdi.le] at hi
  have hdub : d i≤3*D/(2*q) := by
    apply (le_div_iff₀ (by positivity : 0<2*q)).mpr
    have H := ho i hdi
    nlinarith only [H,sq_nonneg (d i)]
  have hmi : c/(12*(N:ℝ))≤ m i := by
    have HX := mul_le_mul_of_nonneg_left hdub (hm i).le
    have HY : c*D/(8*(N:ℝ)*q)≤ m i*(3*D/(2*q)) := hi.trans HX
    have hden : 0<8*(N:ℝ)*q := by positivity
    have HZ := (div_le_iff₀ hden).mp HY
    apply (div_le_iff₀ (by positivity : 0<12*(N:ℝ))).mpr
    have he : m i*(3*D/(2*q))*(8*(N:ℝ)*q)=12*(N:ℝ)*m i*D := by field_simp <;> ring
    rw [he] at HZ
    nlinarith only [HZ,hD]
  have hone : m i*B i≤1 := (Finset.single_le_sum
    (fun j _ => mul_nonneg (hm j).le (hB j)) (Finset.mem_univ i)).trans hcap
  have hBi : B i≤12*(N:ℝ)/c := by
    apply (le_div_iff₀ hc).mpr
    have HH := mul_le_mul_of_nonneg_right hmi (hB i)
    have HH' : c*B i/(12*(N:ℝ))≤1 := by
      calc
        c*B i/(12*(N:ℝ))=c/(12*(N:ℝ))*B i := by ring
        _≤ m i*B i := HH
        _≤1 := hone
    have := (div_le_iff₀ (by positivity : 0<12*(N:ℝ))).mp HH'
    nlinarith only [this]
  exact ⟨i,hdi,hmi,hi,hdub,hBi⟩

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_TemplateRightWeight
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport

lemma template_right_weight {ι : Type*} [Fintype ι] {m B s : ι → ℝ}
    {eta center c : ℝ} (hm : ∀ i,0 ≤  m i) (hsum : ∑ i,m i=1)
    (hB : ∀ i,0 ≤ B i) (hleft : ∀ i,s i < 1-eta → 1 ≤ B i)
    (hcenter : center ≤ 1) (hparameter : c ≤ center-∑ i,m i*B i) :
    c ≤ ∑ i∈Finset.univ.filter (fun i =>  1-eta ≤ s i),m i := by
  classical
  let R := Finset.univ.filter (fun i =>  1-eta ≤ s i)
  let L := Finset.univ.filter (fun i =>  ¬1-eta ≤ s i)
  have hpart : (∑ i∈R,m i)+(∑ i∈L,m i)=1 := by
    rw [show (∑ i∈R,m i)+(∑ i∈L,m i)=∑ i,m i from
      Finset.sum_filter_add_sum_filter_not Finset.univ (fun i =>  1-eta ≤ s i) m,hsum]
  have hbound : (∑ i∈L,m i) ≤ ∑ i,m i*B i := by
    calc
      _ ≤ ∑ i∈L,m i*B i := Finset.sum_le_sum (fun i hi =>  by
        have HB := hleft i (lt_of_not_ge (Finset.mem_filter.mp hi).2)
        simpa using mul_le_mul_of_nonneg_left HB (hm i))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
        (fun i _ _ =>  mul_nonneg (hm i) (hB i))
  change c ≤ ∑ i∈R,m i
  linarith

lemma outward_from_levels {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : Fintype.card ι ≤ n+1) {m d B si : ι → ℝ}
    {q D c eta delta zeta s center : ℝ}
    (hm : ∀ i,0  <  m i) (hsum : ∑ i,m i=1) (hbar : ∑ i,m i*d i=0)
    (hq : 0 < q) (hD : 0 < D) (hc : 0 < c)
    (heta : eta ≤ 1/128) (hdelta : delta ≤ zeta) (hzeta : zeta ≤ 1/16)
    (hs : s < 3/4) (hlow : ∀ i,-2*eta ≤ si i)
    (hrange : ∀ i,|si i-s| ≤ 1+delta)
    (hnorm : ∀ i,|2*q*d i+d i^2+2*D*(si i-s)| ≤ zeta*D)
    (hB : ∀ i,0 ≤ B i) (hleft : ∀ i,si i < 1-eta → 1 ≤ B i)
    (hcenter : center ≤ 1) (hparameter : c ≤ center-∑ i,m i*B i) :
    ∃ i, 0 < d i ∧ c/(12*(n+1:ℝ)) ≤  m i ∧
      c*D/(8*(n+1:ℝ)*q) ≤  m i*d i ∧ d i ≤ 3*D/(2*q) ∧
      -2*eta ≤ si i ∧ si i < 1-eta ∧ B i ≤ 12*(n+1:ℝ)/c := by
  classical
  let R := Finset.univ.filter (fun i =>  1-eta ≤ si i)
  have hzm : zeta*D ≤ D/16 := by nlinarith [mul_le_mul_of_nonneg_right hzeta hD.le]
  have hdm : delta*D ≤ D/16 := by nlinarith [mul_le_mul_of_nonneg_right (hdelta.trans hzeta) hD.le]
  have hem : eta*D ≤ D/128 := by nlinarith [mul_le_mul_of_nonneg_right heta hD.le]
  have hr : ∀ i∈R,2*q*d i+d i^2 ≤ -D/4 := by
    intro i hi
    have hright := (Finset.mem_filter.mp hi).2
    have H := (abs_le.mp (hnorm i)).2
    have HA := mul_le_mul_of_nonneg_left hright hD.le
    have HB := mul_lt_mul_of_pos_left hs hD
    nlinarith only [H,HA,HB,hzm,hem,hD]
  have ho : ∀ i,0 < d i → 2*q*d i+d i^2 ≤ 3*D := by
    intro i hd
    have H := (abs_le.mp (hnorm i)).2
    have HA := mul_le_mul_of_nonneg_left (abs_le.mp (hrange i)).1 hD.le
    nlinarith only [H,HA,hzm,hdm,hD]
  have hcap : ∑ i,m i*B i ≤ 1 := by linarith
  obtain ⟨i,hdi,hmi,hprod,hdub,hBi⟩ := outward_weight_and_cap hn hm hsum hbar hq hD hc R
    (template_right_weight (fun i =>  (hm i).le) hsum hB hleft hcenter hparameter) hr ho hB hcap
  have hir : si i < 1-eta := by
    by_contra H
    have HR := hr i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,le_of_not_gt H⟩)
    have HX := mul_pos hq hdi
    nlinarith only [HR,HX,sq_nonneg (d i),hD]
  push_cast at hmi hprod hBi
  exact ⟨i,hdi,hmi,hprod,hdub,hlow i,hir,hBi⟩

end WeakMTWTransport

end

end

section

noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport

lemma barycenter_opposite_extension {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] (pj : ι → E) (m : ι → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hsum : ∑ i,m i=1) (i : ι)
    {theta : ℝ} (hl : -m i/2 ≤ theta) (hu : theta ≤ 1) :
    (∑ j,m j • pj j)+theta • (pj i-(∑ j,m j • pj j)) ∈ convexHull ℝ (range pj) := by
  classical
  have hmi : m i ≤ 1 := (Finset.single_le_sum (fun j _ => hm j) (Finset.mem_univ i)).trans_eq hsum
  let w : ι → ℝ := fun j => (1-theta)*m j + if j=i then theta else 0
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    dsimp [w]
    by_cases hji : j=i
    · rw [ite_eq_left hji,hji]
      by_cases ht : 0 ≤ theta
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hu) (hm i)) ht
      · have H := mul_le_mul_of_nonneg_right hl (sub_nonneg.mpr hmi)
        nlinarith [sq_nonneg (m i),hm i]
    · rw [ite_eq_right hji,add_zero]
      exact mul_nonneg (sub_nonneg.mpr hu) (hm j)
  have hw1 : ∑ j,w j=1 := by
    dsimp [w]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,hsum]
    simp
  have he : (∑ j,w j • pj j)=(∑ j,m j • pj j)+theta • (pj i-(∑ j,m j • pj j)) := by
    dsimp [w]
    simp_rw [add_smul,mul_smul]
    rw [Finset.sum_add_distrib,←Finset.smul_sum]
    have H : (∑ j,(if j=i then theta else 0) • pj j)=theta • pj i := by
      simp_rw [ite_smul,zero_smul]
      simp
    rw [H]
    module
  rw [←he]
  exact (convex_convexHull ℝ (range pj)).sum_mem (fun j _ => hw j) hw1
    (fun j _ => subset_convexHull ℝ _ (mem_range_self j))

lemma outward_radial_ratio {q D d a theta : ℝ}
    (hq : 0 < q) (ha : 0 < a) (hd : 0 < d)
    (hqa : a*D ≤ q^2) (hdub : d ≤ 3*D/(2*q))
    (ht : -a/3 ≤ theta) :
    q/2 ≤ q+theta*d ∧ d^2/((q+theta*d)*d) ≤ 3/a := by
  have hdq : d*(2*q) ≤ 3*D := (le_div_iff₀ (by positivity : 0 < 2*q)).mp hdub
  have hadq : a*d ≤ 3*q/2 := by
    have H := mul_le_mul_of_nonneg_left hdq ha.le
    nlinarith only [H,hqa,hq]
  have hlow : q/2 ≤ q+theta*d := by
    have H := mul_le_mul_of_nonneg_right ht hd.le
    nlinarith only [H,hadq]
  refine ⟨hlow,?_⟩
  have hqp : 0 < q+theta*d := (half_pos hq).trans_le hlow
  apply (div_le_div_iff₀ (mul_pos hqp hd) ha).mpr
  have H := mul_le_mul_of_nonneg_right hadq hd.le
  have H' := mul_le_mul_of_nonneg_right hlow hd.le
  nlinarith only [H,H']

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActiveDifference
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport
section ActiveDifference
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup E] [Module ℝ E]

omit [DecidableEq ι] in
lemma active_difference_ne_bot {pj : ι → E} {p : E} {m : ι → ℝ}
    {level : E → ℝ} {Bc Bo : ℝ → ℝ} (hsum : ∑ i,m i=1)
    (hprofiles : Bc (level p) ≤ Bo (level p))
    (hparameter : 0 < Bc (level p)-∑ i,m i*Bo (level (pj i))) :
    Submodule.span ℝ (range (fun i => pj i-p))≠⊥ := by
  intro H
  have hpj : ∀ i,pj i=p := by
    intro i
    have HH := (Submodule.subset_span (mem_range_self i) :
      pj i-p∈Submodule.span ℝ (range (fun i => pj i-p)))
    rw [H] at HH
    exact sub_eq_zero.mp HH
  simp_rw [hpj] at hparameter
  rw [←Finset.sum_mul,hsum,one_mul] at hparameter
  linarith

omit [DecidableEq ι] in
lemma line_active_displacements {pj : ι → E} {p e : E} {m : ι → ℝ}
    (hline : Submodule.span ℝ (range (fun i => pj i-p))=Submodule.span ℝ {e})
    (he : e≠0) (hsum : ∑ i,m i=1) (hbar : ∑ i,m i • pj i=p) :
    ∃ d : ι → ℝ, (∀ i,pj i=p+d i • e) ∧ ∑ i,m i*d i=0 := by
  have H : ∀ i,∃ r:ℝ,r • e=pj i-p := by
    intro i
    apply Submodule.mem_span_singleton.mp
    rw [←hline]
    exact Submodule.subset_span (mem_range_self i)
  choose d hd using H
  have hd' : ∀ i,pj i=p+d i • e := by
    intro i
    rw [hd i,add_sub_cancel]
  refine ⟨d,hd',?_⟩
  have Hbar : (∑ i,m i*d i) • e=0 := by
    rw [Finset.sum_smul]
    simp_rw [mul_smul,hd,smul_sub]
    rw [Finset.sum_sub_distrib,←Finset.sum_smul,hsum,one_smul,hbar,sub_self]
  exact (smul_eq_zero.mp Hbar).resolve_right he

end ActiveDifference
end WeakMTWTransport

end

end

section

noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport
section OutwardGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_increment_unit_line {p e : E} (he : ‖e‖=1) (d : ℝ) :
    ‖p+d • e‖^2-‖p‖^2=2*(inner ℝ p e)*d+d^2 := by
  have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he]; norm_num
  rw [←real_inner_self_eq_norm_sq]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right,
    real_inner_comm e p,hee,real_inner_self_eq_norm_sq]
  ring

lemma outward_active_endpoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : Fintype.card ι ≤ n+1) {pj : ι → E} {p e : E}
    {m B si : ι → ℝ} {D c eta delta zeta s center a0 : ℝ}
    (hm : ∀ i,0 < m i) (hsum : ∑ i,m i=1) (hbar : ∑ i,m i • pj i=p)
    (he : ‖e‖=1) (hq : 0 < inner ℝ p e)
    (hline : Submodule.span ℝ (range (fun i => pj i-p))=Submodule.span ℝ {e})
    (hD : 0 < D) (hc : 0 < c) (ha0 : 0 < a0) (hqa : a0*D ≤ (inner ℝ p e)^2)
    (heta : eta ≤ 1/128) (hdelta : delta ≤ zeta) (hzeta : zeta ≤ 1/16)
    (hs : s < 3/4) (hlow : ∀ i,-2*eta ≤ si i)
    (hrange : ∀ i,|si i-s| ≤ 1+delta)
    (hnorm : ∀ i,|‖pj i‖^2-‖p‖^2+2*D*(si i-s)| ≤ zeta*D)
    (hB : ∀ i,0 ≤ B i) (hleft : ∀ i,si i < 1-eta → 1 ≤ B i)
    (hcenter : center ≤ 1) (hparameter : c ≤ center-∑ i,m i*B i) :
    let mstar := c/(12*(n+1:ℝ))
    let theta0 := min (mstar/2) (a0/3)
    ∃ i d, 0 < d ∧ pj i=p+d • e ∧ mstar ≤ m i ∧
      c*D/(8*(n+1:ℝ)*(inner ℝ p e)) ≤ m i*d ∧
      d ≤ 3*D/(2*(inner ℝ p e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧
      B i ≤ 12*(n+1:ℝ)/c ∧ 0 < theta0 ∧
      ∀ theta∈Icc (-theta0) 1,
        p+theta • (pj i-p)∈convexHull ℝ (range pj) ∧
        (inner ℝ p e)/2 ≤ inner ℝ (p+theta • (pj i-p)) e ∧
        ‖pj i-p‖^2/(inner ℝ (p+theta • (pj i-p)) (pj i-p)) ≤ 3/a0 := by
  intro mstar theta0
  have he0 : e≠0 := by intro H; rw [H,norm_zero] at he; norm_num at he
  obtain ⟨d,hd,hbard⟩ := line_active_displacements hline he0 hsum hbar
  have hnorm' : ∀ i,|2*(inner ℝ p e)*d i+d i^2+2*D*(si i-s)| ≤ zeta*D := by
    intro i
    have H := hnorm i
    rwa [hd i,norm_increment_unit_line he (d i)] at H
  obtain ⟨i,hdi,hmi,hprod,hdub,hli,hri,hBi⟩ := outward_from_levels hn hm hsum hbard hq hD hc
    heta hdelta hzeta hs hlow hrange hnorm' hB hleft hcenter hparameter
  have hmstar : 0 < mstar := by dsimp [mstar] <;> positivity
  have ht0 : 0 < theta0 := lt_min (half_pos hmstar) (by positivity)
  refine ⟨i,d i,hdi,hd i,hmi,hprod,hdub,hli,hri,hBi,ht0,?_⟩
  intro theta htheta
  have hlowtheta : -m i/2 ≤ theta := by
    have HH : theta0 ≤ mstar/2 := min_le_left _ _
    linarith only [htheta.1,HH,hmi]
  have hthetaa : -a0/3 ≤ theta := by
    have HH : theta0 ≤ a0/3 := min_le_right _ _
    linarith only [htheta.1,HH]
  have Hconv := barycenter_opposite_extension pj m (fun j => (hm j).le) hsum i hlowtheta htheta.2
  rw [hbar] at Hconv
  have hpie : pj i-p=d i • e := by rw [hd i]; module
  have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he]; norm_num
  have Hrad := outward_radial_ratio hq ha0 hdi hqa hdub hthetaa
  refine ⟨Hconv,?_,?_⟩
  · simpa only [hpie,inner_add_left,real_inner_smul_left,hee,mul_one] using Hrad.1
  · have Hn : ‖pj i-p‖^2=d i^2 := by
      rw [hpie,norm_smul,he,mul_one,Real.norm_eq_abs,sq_abs]
    have Hi : inner ℝ (p+theta • (pj i-p)) (pj i-p)=
        (inner ℝ p e+theta*d i)*d i := by
      rw [hpie]
      simp only [inner_add_left,inner_smul_right,real_inner_smul_left,hee]
      ring
    rw [Hn,Hi]
    exact Hrad.2

end OutwardGeometry
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_UpperJacobianBarrier
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Module

namespace WeakMTWTransport
section CenterRank
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma unit_positive_direction_of_rank_one_semibound (S : Submodule ℝ E)
    {p : E} {a b : ℝ} (ha : 0 < a) (hS : S≠⊥)
    (hbound : ∀ z ∈ S, a*‖z‖^2 ≤ b*(inner ℝ p z)^2) :
    ∃ e ∈ S, ‖e‖=1 ∧ 0 < inner ℝ p e ∧
      S=Submodule.span ℝ {e} ∧ a ≤ b*(inner ℝ p e)^2 := by
  have hk : ∀ z ∈ S, inner ℝ p z=0 → z=0 := by
    intro z hz hpz
    have H := hbound z hz
    rw [hpz,zero_pow (by norm_num : 2≠0),mul_zero] at H
    have Hsq : ‖z‖^2 ≤ 0 := (mul_le_mul_iff_of_pos_left ha).mp (by simpa only [mul_zero] using H)
    exact norm_eq_zero.mp (by nlinarith only [Hsq,norm_nonneg z,sq_nonneg ‖z‖])
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hpv : inner ℝ p v≠0 := fun H => hv0 (hk v hv H)
  obtain ⟨w,hw,hw0,hpw⟩ : ∃ w:E,w∈S ∧ w≠0 ∧ 0 < inner ℝ p w := by
    rcases lt_or_gt_of_ne hpv with h | h
    · exact ⟨-v,S.neg_mem hv,neg_ne_zero.mpr hv0,by simpa using neg_pos.mpr h⟩
    · exact ⟨v,hv,hv0,h⟩
  let e : E := ‖w‖⁻¹ • w
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have heS : e∈S := S.smul_mem _ hw
  have hen : ‖e‖=1 := by dsimp [e]; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hwn.le),inv_mul_cancel₀ hwn.ne']
  have hpe : 0 < inner ℝ p e := by
    change 0 < inner ℝ p (‖w‖⁻¹ • w)
    rw [inner_smul_right]
    exact mul_pos (inv_pos.mpr hwn) hpw
  have hspan : S=Submodule.span ℝ {e} := by
    apply le_antisymm
    · intro z hz
      have heq : z=((inner ℝ p z)/(inner ℝ p e)) • e := by
        apply sub_eq_zero.mp
        apply hk _ (S.sub_mem hz (S.smul_mem _ heS))
        rw [inner_sub_right,inner_smul_right,div_mul_cancel₀ _ hpe.ne',sub_self]
      rw [heq]
      exact (Submodule.span ℝ {e}).smul_mem _ (Submodule.subset_span (mem_singleton e))
    · exact Submodule.span_le.mpr (singleton_subset_iff.mpr heS)
  refine ⟨e,heS,hen,hpe,hspan,?_⟩
  simpa only [hen,one_pow,mul_one] using hbound e heS
end CenterRank
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_FirstRank
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
section FirstRank
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
lemma ChartFixedPrefixLimit.positive_rank_direction
    {a:M} {v G:M → ℝ} {t:ℝ}
    {q:ℕ → subgradientGraph (n := n) (cTransform v)}
    {q₀:subgradientGraph (n := n) (cTransform v)}
    (J:ChartFixedPrefixLimit a v G t q q₀)
    (hbase:q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let b:=graphBaseCoordinate a q₀.1
    let p:=graphVelocityCoordinate a q₀.1
    let E:=TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
    let κ:Type:={i:Fin (Module.finrank ℝ (Model n)+1) // 0<J.w₀ i}
    let pj:κ → E:=fun i=>chartFiberInverse a b (J.pj₀ i)
    let P:E:=chartFiberInverse a b p
    let S:=Submodule.span ℝ (range (fun i=>pj i-P))
    ∀ (A C:ℝ),0<A →
    (∀d:Model n,A*‖chartFiberInverse a b d‖^2+
      C*(inner ℝ P (chartFiberInverse a b d))^2≤J.H d d) →
    ∀ (level:E → ℝ) (Bc Bo:ℝ → ℝ),
    Bc (level P)≤Bo (level P) →
    0<Bc (level P)-∑ i,J.w₀ i*Bo (level (chartFiberInverse a b (J.pj₀ i))) →
    ∃ e∈S,‖e‖=1 ∧ 0 < inner ℝ P e ∧ S=Submodule.span ℝ {e} ∧ A≤(-C)*(inner ℝ P e)^2 := by
  dsimp only
  let b:=graphBaseCoordinate a q₀.1
  let p:=graphVelocityCoordinate a q₀.1
  let x:=(extChartAt 𝓘(ℝ,Model n) a).symm b
  let E:=TangentSpace 𝓘(ℝ,Model n) x
  let T:=trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  let U:=chartFiberInverse a b
  let V:=T.continuousLinearMapAt ℝ x
  let κ:Type:={i:Fin (Module.finrank ℝ (Model n)+1) // 0<J.w₀ i}
  let pj:κ → E:=fun i=>U (J.pj₀ i)
  let P:E:=U p
  let S:=Submodule.span ℝ (range (fun i=>pj i-P))
  have hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source hbase
  have hx : x∈T.baseSet := by
    simpa only [x,T,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  have hUV (d:E):U (V d)=d := T.symmL_continuousLinearMapAt (R := ℝ) hx d
  have hVU (d:Model n):V (U d)=d := T.continuousLinearMapAt_symmL (R := ℝ) hx d
  intro A C hA hbound level Bc Bo hprofiles hparameter
  have hres:=positive_barycentric_restriction (fun i=>U (J.pj₀ i)) J.w₀ J.nonnegLimit J.totalLimit
  let : Nonempty κ:=hres.1
  have hparam:0<Bc (level P)-∑ i:κ,J.w₀ i*Bo (level (pj i)) := by
    rwa [hres.2.2.2 (fun i=>Bo (level (U (J.pj₀ i))))]
  classical
  have hS:S≠⊥:=active_difference_ne_bot hres.2.1 hprofiles hparam
  let L:E →L[ℝ] E →L[ℝ] ℝ:=J.L.bilinearComp V V
  have hk:S≤LinearMap.ker L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change L (pj i-P)=0
    ext d
    change J.L (V (U (J.pj₀ i)-U p)) (V d)=0
    rw [map_sub,hVU,hVU]
    exact J.kernel i (V d)
  apply unit_positive_direction_of_rank_one_semibound S hA hS
  intro d hd
  have hl:L d=0 := hk hd
  have hzero:J.L (V d) (V d)=0 := congrArg (fun f:E →L[ℝ] ℝ=>f d) hl
  have HH:=hbound (V d)
  rw [hUV] at HH
  have HU:=J.upper (V d)
  rw [hzero] at HU
  linarith only [HH,HU]

end FirstRank
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumFamily.limit_coordinates {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo)
    {Q:TangentBundle 𝓘(ℝ,Model n) M}
    (hQ : Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 Q)) :
    Tendsto (fun k=>graphBaseCoordinate Q.1 (F.row k).q.1) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) Q.1 Q.1)) ∧
    Tendsto (fun k=>graphVelocityCoordinate Q.1 (F.row k).q.1) atTop (𝓝 (show Model n from Q.2)) ∧
    Tendsto F.z atTop (𝓝 (riemannianExp Q.1 Q.2)) ∧
    Tendsto (fun k=>riemannianExp (F.row k).q.1.1 (F.row k).q.1.2) atTop
      (𝓝 (riemannianExp Q.1 Q.2)) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (⟨Q.1,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hs : Q∈χ.source := (tangent_chart_source_iff _ _).mpr (mem_extChartAt_source Q.1)
  have HC := ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds hs)).tendsto.comp hQ
  have hvel : Tendsto (fun k=>graphVelocityCoordinate Q.1 (F.row k).q.1) atTop
      (𝓝 (graphVelocityCoordinate Q.1 Q)) := HC.snd_nhds
  rw [graph_coordinates_at_center] at hvel
  have HE := contMDiff_riemannianExp.continuous.tendsto Q |>.comp hQ
  have HP := (contMDiff_riemannianExp.continuous.comp contMDiff_tangentScale.continuous).tendsto (1,Q)
    |>.comp (F.time.prodMk_nhds hQ)
  have HZ : Tendsto F.z atTop (𝓝 (riemannianExp Q.1 Q.2)) := by
    change Tendsto (fun k=>riemannianExp (F.row k).q.1.1 (F.t k • (F.row k).q.1.2)) atTop
      (𝓝 (riemannianExp Q.1 ((1:ℝ) • Q.2))) at HP
    simp only [one_smul] at HP
    exact HP.congr (fun k=>(F.row k).projection)
  exact ⟨HC.fst_nhds,hvel,HZ,HE⟩
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_ModelTangentJet
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
section ModelTangentJet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma center_frame_identity (a : M) (d : Model n) :
    (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ a d=d := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) a)]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source a)

end ModelTangentJet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FrameMetric
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
section FrameMetric
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma frameMetric_apply {a:M} {b:Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (d e:Model n) :
    frameMetric a b d e=inner ℝ (chartFiberInverse a b d) (chartFiberInverse a b e) := by
  have hp : (1:ℝ) • chartFiberInverse a b 0∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) := by
    simpa only [map_zero,smul_zero] using zero_mem_injectivityDomain
      (n := n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  simpa only [frameMetric,chartFiberInverse,one_mul] using movingPrefixEnergy_hessian hb hp d e

omit [Nonempty M] in
lemma frameMetric_continuousAt {a:M} {b:Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) : ContinuousAt (frameMetric a) b := by
  have hp : (1:ℝ) • chartFiberInverse a b 0∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) := by
    simpa only [map_zero,smul_zero] using zero_mem_injectivityDomain
      (n := n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  have H := (ContDiffAt.partial_snd_fderiv_two (movingPrefixEnergy_contDiffAt hb hp)).continuousAt
  exact ContinuousAt.comp (f := fun z:Model n=>(z,(0:Model n))) H
    (show ContinuousAt (fun z:Model n=>(z,(0:Model n))) b from
    continuousAt_id.prodMk continuousAt_const)

omit [Nonempty M] in
lemma frameMetric_center (a:M) (d e:Model n) :
    frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d e=
      inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from d) e := by
  rw [frameMetric_apply ((extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a))]
  have ha := (extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)
  dsimp only [chartFiberInverse]
  rw [ha,center_frame_identity,center_frame_identity]

omit [Nonempty M] in
lemma frameMetric_center_coercive (a:M) : ∃ δ>0,∀ d:Model n,
    δ*‖d‖^2≤frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d := by
  let T := trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  let A := T.continuousLinearMapAt ℝ a
  let K := ‖A‖+1
  have hK : 0<K := by dsimp [K] <;> positivity
  refine ⟨1/K^2,by positivity,?_⟩
  intro d
  have hid : A (show TangentSpace 𝓘(ℝ,Model n) a from d)=d := by
    have H := T.continuousLinearMapAt_symmL (R := ℝ) (mem_baseSet_trivializationAt (Model n)
      (TangentSpace 𝓘(ℝ,Model n)) a) d
    simpa only [T,center_frame_identity] using H
  have hnorm := A.le_opNorm (show TangentSpace 𝓘(ℝ,Model n) a from d)
  rw [hid] at hnorm
  have hnorm' : ‖d‖≤K*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖ :=
    hnorm.trans (mul_le_mul_of_nonneg_right (by dsimp [K] <;> linarith) (norm_nonneg _))
  rw [frameMetric_center,real_inner_self_eq_norm_sq]
  have H := pow_le_pow_left₀ (norm_nonneg d) hnorm' 2
  rw [mul_pow] at H
  calc
    1/K^2*‖d‖^2 = ‖d‖^2/K^2 := by ring
    _ ≤ ‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2 :=
      (div_le_iff₀ (sq_pos_of_pos hK)).mpr (by nlinarith only [H])

end FrameMetric
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FrameAbsorption
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
section FrameAbsorption
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma eventual_frame_rank_lower {a:M} {b p:ℕ → Model n} {q:Model n}
    {H:ℕ → Model n →L[ℝ] Model n →L[ℝ] ℝ} {A C:ℝ} (hA:0<A)
    (hb:Tendsto b atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hp:Tendsto p atTop (𝓝 q))
    (hH:∀ ε:ℝ,0<ε → ∀ᶠ k in atTop,∀d:Model n,
      A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
        C*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2≤H k d d) :
    ∀ᶠ k in atTop,∀d:Model n,
      A/2*‖chartFiberInverse a (b k) d‖^2+
        C*(inner ℝ (chartFiberInverse a (b k) (p k)) (chartFiberInverse a (b k) d))^2≤H k d d := by
  let b₀ := extChartAt 𝓘(ℝ,Model n) a a
  have hb₀ : b₀∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hG := (frameMetric_continuousAt hb₀).tendsto.comp hb
  have hR := covectorSquare_continuous.tendsto (frameMetric a b₀ q) |>.comp (tendsto_clm_apply hG hp)
  obtain ⟨δ,hδ,hcoer⟩ := frameMetric_center_coercive (n := n) a
  have HH : ∀ε:ℝ,0<ε → ∀ᶠ k in atTop,∀d:Model n,
      A*frameMetric a b₀ d d+C*covectorSquare (frameMetric a b₀ q) d d-ε*‖d‖^2≤H k d d := by
    intro ε he
    filter_upwards [hH ε he] with k hk
    intro d
    have hself : frameMetric a b₀ d d=‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2 := by
      exact (frameMetric_center a d d).trans
        (real_inner_self_eq_norm_sq (show TangentSpace 𝓘(ℝ,Model n) a from d))
    simpa only [hself,covectorSquare_apply,frameMetric_center,←sq,b₀] using hk d
  have HG := eventual_moving_rank_lower hA hδ hcoer hG hR HH
  have ht : ∀ᶠ k in atTop,b k∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    hb.eventually ((isOpen_extChartAt_target a).mem_nhds hb₀)
  filter_upwards [HG,ht] with k hk hbk
  intro d
  simpa only [Function.comp_def,covectorSquare_apply,frameMetric_apply hbk,real_inner_self_eq_norm_sq,←sq] using hk d

end FrameAbsorption
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MaximumRank
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
section MaximumRank
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumJensenFamily.eventual_rank_of_center_lower
    {hmtw:WeakMTW (n := n) (M := M)} {v:M → ℝ} {hv:Continuous v}
    {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n := n) v α D bminus bplus Bc Bo}
    (hm:0 ≤ bminus) (hp:0 < bplus) (hprofiles:∀s,Bc s ≤ Bo s)
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    {q:Model n} (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {A C:ℝ} (hA:0 < A)
    (hH:∀ ε:ℝ,0 < ε → ∀ᶠ k in atTop,∀d:Model n,
      A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
        C*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤
          (J.first k).H d d) :
    ∀ᶠ k in atTop,
      let b:=graphBaseCoordinate a (F.row k).q.1
      let p:=graphVelocityCoordinate a (F.row k).q.1
      let E:=TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
      let κ:Type:={i:Fin (Module.finrank ℝ (Model n)+1) // 0 < (J.first k).w₀ i}
      let pj:κ → E:=fun i=>chartFiberInverse a b ((J.first k).pj₀ i)
      let P:E:=chartFiberInverse a b p
      let S:=Submodule.span ℝ (range (fun i=>pj i-P))
      ∃ e∈S,‖e‖=1 ∧ 0 < inner ℝ P e ∧ S=Submodule.span ℝ {e} ∧
        A/2 ≤ (-C)*(inner ℝ P e)^2 := by
  obtain ⟨hb,hpcoord,_,_⟩:=F.limit_coordinates hQ
  have H:=eventual_frame_rank_lower hA hb hpcoord hH
  filter_upwards [H] with k hk
  let b:=graphBaseCoordinate a (F.row k).q.1
  let E:=TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  let level:E → ℝ:=fun r=>(v (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) r)-α)/D
  have hbt:b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (J.poleSource k)
  have Hb:0 ≤ F.b k:=hm.trans (F.parameter k).1.le
  have Hpos:0 < (1:ℝ)/4096+4*F.b k/bplus := by positivity
  have HP:0 < Bc (level (chartFiberInverse a b (graphVelocityCoordinate a (F.row k).q.1)))-
      ∑ i,(J.first k).w₀ i*Bo (level (chartFiberInverse a b ((J.first k).pj₀ i))) := by
    have HP:=(F.row k).chart_first_limit_parameter (J.poleSource k) (J.first k)
    change 1/4096+4*F.b k/bplus ≤
      Bc ((v (movingNormal a (b,graphVelocityCoordinate a (F.row k).q.1))-α)/D)-
        ∑ i,(J.first k).w₀ i*Bo ((v (movingNormal a (b,(J.first k).pj₀ i))-α)/D) at HP
    simp only [movingNormal_eq hbt] at HP
    exact Hpos.trans_le HP
  exact (J.first k).positive_rank_direction (J.poleSource k) (A/2) C (half_pos hA) hk
    level Bc Bo (hprofiles _) HP

end MaximumRank
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SectionOscillation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

section SectionOscillation
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

omit [Nonempty M] in
lemma isCompact_gapSection {u v : M → ℝ} (hv : Continuous v) (x : M) (r : ℝ) :
    IsCompact (gapSection u v x r) := by
  apply IsClosed.isCompact
  exact isClosed_le ((continuous_const.add (continuous_cost_right x)).add hv) continuous_const

lemma gapSection_nonempty {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    (gapSection u v x r).Nonempty := by
  obtain ⟨y, hy⟩ := dualPair_contact_left hv huv x
  exact ⟨y, by simpa only [gapSection, mem_ofPred_eq, hy] using hr⟩

lemma sectionOscillation_extrema {u v : M → ℝ} (hv : Continuous v)
    (huv : IsCostDualPair u v) (x : M) {r : ℝ} (hr : 0 ≤ r) :
    ∃ y0 ∈ gapSection u v x r, ∃ y1 ∈ gapSection u v x r,
      (∀ y ∈ gapSection u v x r, v y0 ≤ v y) ∧
      (∀ y ∈ gapSection u v x r, v y ≤ v y1) ∧
      sectionOscillation u v x r = v y1 - v y0 := by
  have hc := isCompact_gapSection (u := u) hv x r
  have hn := gapSection_nonempty hv huv x hr
  obtain ⟨y0, hy0, hmin⟩ := hc.exists_isMinOn hn hv.continuousOn
  obtain ⟨y1, hy1, hmax⟩ := hc.exists_isMaxOn hn hv.continuousOn
  have hleast : IsLeast (v '' gapSection u v x r) (v y0) := by
    refine ⟨mem_image_of_mem v hy0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmin hy
  have hgreatest : IsGreatest (v '' gapSection u v x r) (v y1) := by
    refine ⟨mem_image_of_mem v hy1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  exact ⟨y0, hy0, y1, hy1, fun _ hy => hmin hy, fun _ hy => hmax hy,
    by rw [sectionOscillation, hleast.csInf_eq, hgreatest.csSup_eq]⟩

end SectionOscillation

open Filter

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ModifiedData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
section ModifiedData
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma modified_transform_bounds {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a D b H : ℝ} {B : ℝ → ℝ}
    (hB : Continuous B) (hb : 0 ≤ b) (hbound : ∀ s,0 ≤ B s ∧ B s ≤ H) (x : M) :
    u x-b*H ≤ cTransform (modifiedDatum v a D b B) x ∧
      cTransform (modifiedDatum v a D b B) x ≤ u x := by
  have hw := continuous_modifiedDatum hv a D b hB
  have hshift : Continuous (fun y => v y+b*H) := by
    rw [hdual.2]
    exact (continuous_cTransform hu).add continuous_const
  have h1 := cTransform_antitone (w := fun y => v y+b*H) hw hshift
    (fun y => add_le_add_right (mul_le_mul_of_nonneg_left (hbound _).2 hb) (v y)) x
  have h2 := cTransform_antitone hv hw
    (fun y => le_add_of_nonneg_right (mul_nonneg hb (hbound _).1)) x
  rw [cTransform_add_const hv,hdual.1.symm] at h1
  rw [hdual.1.symm] at h2
  exact ⟨h1,h2⟩

lemma modified_double_bounds {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a D b : ℝ} {B : ℝ → ℝ}
    (hB : Continuous B) (hb : 0 ≤ b) (hbound : ∀ s,0 ≤ B s) (y : M) :
    v y ≤ cTransform (cTransform (modifiedDatum v a D b B)) y ∧
      cTransform (cTransform (modifiedDatum v a D b B)) y ≤ modifiedDatum v a D b B y := by
  have hw := continuous_modifiedDatum hv a D b hB
  have h1 := cTransform_antitone hv hw
    (fun y => le_add_of_nonneg_right (mul_nonneg hb (hbound _)))
  rw [←hdual.1] at h1
  have h2 := cTransform_antitone (continuous_cTransform hw) hu h1 y
  rw [←hdual.2] at h2
  exact ⟨h2,cTransform_cTransform_le hw y⟩

lemma modified_excess_upper {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a D b : ℝ} {Bc Bo : ℝ → ℝ}
    (hBo : Continuous Bo) (hb : 0 ≤ b) (ho : ∀ s,0 ≤ Bo s) (hc : ∀ s,Bc s ≤ 1)
    (y : M) : modifiedExcess v a D b Bc Bo y ≤ b := by
  have H := (modified_double_bounds (a := a) (D := D) hu hv hdual hBo hb ho y).1
  have Hc := mul_le_mul_of_nonneg_left (hc ((v y-a)/D)) hb
  dsimp only [modifiedExcess,modifiedDatum]
  linarith

lemma modified_contact_original_section {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a D b H : ℝ} {B : ℝ → ℝ}
    (hB : Continuous B) (hb : 0 ≤ b) (hbound : ∀ s,0 ≤ B s ∧ B s ≤ H) {x y : M}
    (hc : contactGap (cTransform (modifiedDatum v a D b B)) (modifiedDatum v a D b B) x y=0) :
    contactGap u v x y ≤ b*H := by
  have Hg := (modified_transform_bounds (a := a) (D := D) hu hv hdual hB hb hbound x).1
  have Ho := mul_nonneg hb (hbound ((v y-a)/D)).1
  dsimp only [contactGap,modifiedDatum] at hc ⊢
  linarith only [Hg,Ho,hc]

omit [CompactSpace M] [Nonempty M] in
lemma modified_excess_at_contact {v : M → ℝ} {a D b : ℝ} {Bc Bo : ℝ → ℝ} {x y : M}
    (hc : contactGap (cTransform (modifiedDatum v a D b Bo))
      (cTransform (cTransform (modifiedDatum v a D b Bo))) x y=0) :
    modifiedExcess v a D b Bc Bo y =
      v y+b*Bc ((v y-a)/D)+cost x y+cTransform (modifiedDatum v a D b Bo) x := by
  dsimp only [contactGap] at hc
  dsimp only [modifiedExcess,modifiedDatum]
  linarith only [hc]

end ModifiedData
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActualLevels
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
section ActualLevels
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma contact_of_global_support {g : M → ℝ} (hg : Continuous g) {x y : M}
    (hs : ∀ a,g x+cost x y ≤ g a+cost a y) :
    contactGap g (cTransform g) x y=0 := by
  have hupper : cTransform g y ≤  -g x-cost x y := by
    rw [cTransform_le_iff hg]
    intro a
    rw [cost_symm y a]
    linarith only [hs a]
  have hlower := cTransform_gap_nonneg hg y x
  rw [contactGap,cost_symm y x] at hlower
  dsimp only [contactGap]
  linarith only [hupper,hlower]

lemma WeakMTW.modified_aligned_levels (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {a D b H : ℝ} {Bc Bo : ℝ → ℝ} (ho : Continuous Bo) (hb : 0 ≤ b)
    (hob : ∀ s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb : ∀ s,-1 ≤ Bc s ∧ Bc s ≤ 1)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (modifiedDatum v a D b Bo) x)) :
    let y := riemannianExp x p
    y ∈ gapSection u v x ((H+2)*b) ∧
    ∀ pi ∈ activeLogs (n := n) (modifiedDatum v a D b Bo) x,
      riemannianExp x pi ∈ gapSection u v x ((H+2)*b) ∧
      v (riemannianExp x pi)-v y=(‖p‖^2-‖pi‖^2)/2+
        b*(Bc ((v y-a)/D)-Bo ((v (riemannianExp x pi)-a)/D))-
        modifiedExcess v a D b Bc Bo y := by
  dsimp only
  have hw := continuous_modifiedDatum hv a D b ho
  obtain ⟨hpm,hs⟩ := hmtw.active_hull_global_support hw hp
  have hcontact := contact_of_global_support (continuous_cTransform hw) hs
  have he := modified_excess_at_contact (Bc := Bc) hcontact
  have hupp := modified_excess_upper (a := a) (D := D) hu hv hdual ho hb (fun s=>(hob s).1)
    (fun s=>(hcb s).2) (riemannianExp x p)
  have hg := (modified_transform_bounds (a := a) (D := D) hu hv hdual ho hb hob x).1
  have hc := mul_le_mul_of_nonneg_left (hcb ((v (riemannianExp x p)-a)/D)).1 hb
  refine ⟨?_,?_⟩
  · change contactGap u v x (riemannianExp x p) ≤ (H+2)*b
    dsimp only [contactGap]
    linarith only [he,hupp,hg,hc]
  · intro pi hi
    refine ⟨?_,?_⟩
    · have HA := modified_contact_original_section hu hv hdual ho hb hob hi.2
      change contactGap u v x (riemannianExp x pi) ≤ (H+2)*b
      linarith only [HA,hb]
    · have hai := hi.2
      change cTransform (modifiedDatum v a D b Bo) x+cost x (riemannianExp x pi)+
        (v (riemannianExp x pi)+b*Bo ((v (riemannianExp x pi)-a)/D))=0 at hai
      have hpn : cost x (riemannianExp x p)=‖p‖^2/2 := by rw [cost,hpm]
      have hin : cost x (riemannianExp x pi)=‖pi‖^2/2 := by rw [cost,hi.1]
      rw [hpn] at he
      rw [hin] at hai
      linarith only [he,hai]

lemma modified_positive_excess_center_level {u v : M → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {a D b : ℝ} {Bc Bo : ℝ → ℝ} (ho : Continuous Bo) (hb : 0 ≤ b)
    (hob : ∀ s,0 ≤ Bo s) (hright : ∀ s,3/4 ≤ s → Bc s ≤ 0) {y : M}
    (he : 0 < modifiedExcess v a D b Bc Bo y) : (v y-a)/D < 3/4 := by
  have hl := (modified_double_bounds (a := a) (D := D) hu hv hdual ho hb hob y).1
  by_contra h
  have hh := mul_nonpos_of_nonneg_of_nonpos hb (hright _ (le_of_not_gt h))
  dsimp only [modifiedExcess,modifiedDatum] at he
  linarith only [he,hl,hh]

lemma section_level_range {u v : M → ℝ} (hv : Continuous v) (hdual : IsCostDualPair u v)
    {x y z : M} {r a D delta : ℝ} (hr : 0 ≤ r) (hD : 0 < D)
    (hy : y ∈ gapSection u v x r) (hz : z ∈ gapSection u v x r)
    (hosc : sectionOscillation u v x r ≤ (1+delta)*D) :
    |(v y-a)/D-(v z-a)/D| ≤ 1+delta := by
  obtain ⟨y0,_,y1,_,hl,hu,he⟩ := sectionOscillation_extrema hv hdual x hr
  have hyy0 := hl y hy
  have hyy1 := hu y hy
  have hzz0 := hl z hz
  have hzz1 := hu z hz
  rw [he] at hosc
  rw [←sub_div,abs_div,abs_of_pos hD]
  apply (div_le_iff₀ hD).mpr
  apply abs_le.mpr
  constructor  <;> linarith only [hyy0,hyy1,hzz0,hzz1,hosc]

lemma limiting_levels_lower {ι : Type*} [Fintype ι] {m si : ι → ℝ}
    {Bc Bo : ℝ → ℝ} {s eta delta c : ℝ}
    (hm : ∀ i,0 ≤ m i) (hsum : ∑ i,m i=1)
    (hBo : ∀ r,0 ≤ Bo r) (hleft : ∀ r,r < 1-eta → 1 ≤ Bo r)
    (hBc : Bc s ≤ 1) (hc : 0 < c) (hparameter : c ≤ Bc s-∑ i,m i*Bo (si i))
    (hrange : ∀ i j,|si i-si j| ≤ 1+delta) (hcenter : ∀ i,|s-si i| ≤ 1+delta)
    (hdelta : delta ≤ eta) :
    -2*eta ≤ s ∧ ∀ i,-2*eta ≤ si i := by
  classical
  have H := template_right_weight hm hsum (fun i=>hBo (si i))
    (fun i=>hleft (si i)) hBc hparameter
  obtain ⟨j,hj,_⟩ := Finset.sum_pos_iff_of_nonneg (fun i _=>hm i) |>.mp (hc.trans_le H)
  have hright := (Finset.mem_filter.mp hj).2
  refine ⟨?_,?_⟩
  · have hsc := (abs_le.mp (hcenter j)).1
    linarith only [hsc,hright,hdelta]
  · intro i
    have hsi := (abs_le.mp (hrange i j)).1
    linarith only [hsi,hright,hdelta]

end ActualLevels
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActualOutward
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
section ActualOutward
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.actual_outward_endpoint (hmtw:WeakMTW (n := n) (M := M))
    {u v:M → ℝ} (hu:Continuous u) (hv:Continuous v) (hdual:IsCostDualPair u v)
    {α D b H:ℝ} {Bc Bo:ℝ → ℝ} (ho:Continuous Bo) (hb:0 ≤ b)
    (hob:∀s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb:∀s,-1 ≤ Bc s ∧ Bc s ≤ 1)
    (hright:∀s,3/4 ≤ s → Bc s ≤ 0)
    {ι:Type} [Fintype ι] [DecidableEq ι] {N:ℕ} (hN:Fintype.card ι ≤ N+1)
    {x:M} {p e:TangentSpace 𝓘(ℝ,Model n) x}
    {pj:ι → TangentSpace 𝓘(ℝ,Model n) x} {m:ι → ℝ}
    (hm:∀i,0 < m i) (hsum:∑ i,m i=1) (hbar:∑ i,m i • pj i=p)
    (hactive:∀i,pj i∈activeLogs (modifiedDatum v α D b Bo) x)
    (he:‖e‖=1) (hq:0  <  inner ℝ p e)
    (hline:Submodule.span ℝ (range (fun i=>pj i-p))=Submodule.span ℝ {e})
    {c eta delta zeta a0:ℝ} (hD:0 < D) (hc:0 < c) (ha0:0 < a0)
    (hqa:a0*D ≤ (inner ℝ p e)^2) (heta:eta ≤ 1/128) (hdelta:delta ≤ zeta)
    (hdeltaEta:delta ≤ eta) (hzeta:zeta ≤ 1/16)
    (hleft:∀s,s < 1-eta → 1 ≤ Bo s)
    (hexcess:0 < modifiedExcess v α D b Bc Bo (riemannianExp x p))
    (herror:2*(H+2)*b ≤ zeta*D)
    (hosc:sectionOscillation u v x ((H+2)*b) ≤ (1+delta)*D)
    (hparameter:c ≤ Bc ((v (riemannianExp x p)-α)/D)-
      ∑ i,m i*Bo ((v (riemannianExp x (pj i))-α)/D)) :
    let si:=fun i=>(v (riemannianExp x (pj i))-α)/D
    let mstar:=c/(12*(N+1:ℝ))
    let theta0:=min (mstar/2) (a0/3)
    ∃ i d,0 < d ∧ pj i=p+d • e ∧ mstar ≤ m i ∧
      c*D/(8*(N+1:ℝ)*(inner ℝ p e)) ≤ m i*d ∧
      d ≤ 3*D/(2*(inner ℝ p e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧
      Bo (si i) ≤ 12*(N+1:ℝ)/c ∧ 0 < theta0 ∧
      ∀ theta∈Icc (-theta0) 1,
        p+theta • (pj i-p)∈convexHull ℝ (range pj) ∧
        (inner ℝ p e)/2 ≤ inner ℝ (p+theta • (pj i-p)) e ∧
        ‖pj i-p‖^2/(inner ℝ (p+theta • (pj i-p)) (pj i-p)) ≤ 3/a0 := by
  dsimp only
  let y:=riemannianExp x p
  let si:=fun i=>(v (riemannianExp x (pj i))-α)/D
  let s:=(v y-α)/D
  have hp:p∈convexHull ℝ (activeLogs (modifiedDatum v α D b Bo) x) := by
    rw [←hbar]
    exact (convex_convexHull ℝ _).sum_mem (fun i _=>(hm i).le) hsum
      (fun i _=>subset_convexHull ℝ _ (hactive i))
  obtain ⟨hy,Hlevels⟩:=hmtw.modified_aligned_levels hu hv hdual ho hb hob hcb hp
  have hH:0 ≤ H:=(hob 0).1.trans (hob 0).2
  have hr:0 ≤ (H+2)*b:=mul_nonneg (by linarith) hb
  have hrange:∀i j,|si i-si j| ≤ 1+delta := fun i j=>
    section_level_range hv hdual hr hD (Hlevels (pj i) (hactive i)).1
      (Hlevels (pj j) (hactive j)).1 hosc
  have hcenter:∀i,|s-si i| ≤ 1+delta := fun i=>
    section_level_range hv hdual hr hD hy (Hlevels (pj i) (hactive i)).1 hosc
  have hlow:=limiting_levels_lower (fun i=>(hm i).le) hsum (fun r=>(hob r).1) hleft
    (hcb s).2 hc hparameter hrange hcenter hdeltaEta
  have hs:s < 3/4:=modified_positive_excess_center_level hu hv hdual ho hb
    (fun r=>(hob r).1) hright hexcess
  have herr:∀i,|‖pj i‖^2-‖p‖^2+2*D*(si i-s)| ≤ zeta*D := by
    intro i
    have Hlev: v (riemannianExp x (pj i))-v y=(‖p‖^2-‖pj i‖^2)/2+
        b*(Bc s-Bo (si i))-modifiedExcess v α D b Bc Bo y :=
      (Hlevels (pj i) (hactive i)).2
    have Hdiv:D*(si i-s)=v (riemannianExp x (pj i))-v y := by
      dsimp only [si,s]
      field_simp
      ring
    have Hup:=modified_excess_upper (a := α) (D := D) hu hv hdual ho hb (fun r=>(hob r).1)
      (fun r=>(hcb r).2) y
    have Hcb:=mul_le_mul_of_nonneg_left (hcb s).1 hb
    have Hct:=mul_le_mul_of_nonneg_left (hcb s).2 hb
    have Hob:=mul_le_mul_of_nonneg_left (hob (si i)).2 hb
    have Hoz:=mul_nonneg hb (hob (si i)).1
    have hHb:=mul_nonneg hH hb
    apply abs_le.mpr
    constructor  <;>  nlinarith only [Hlev,Hdiv,Hup,hexcess,Hcb,Hct,Hob,Hoz,herror,hHb,hb]
  apply outward_active_endpoint hN hm hsum hbar he hq hline hD hc ha0 hqa heta hdelta hzeta
    hs hlow.2 ?_ herr (fun i=>(hob (si i)).1) (fun i=>hleft (si i)) (hcb s).2 hparameter
  intro i
  simpa only [abs_sub_comm] using hcenter i

end ActualOutward
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FirstOutward
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
section FirstOutward
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma ChartFixedPrefixLimit.outward_endpoint
    (hmtw:WeakMTW (n := n) (M := M))
    {u v G:M → ℝ} (hu:Continuous u) (hv:Continuous v) (hdual:IsCostDualPair u v)
    {α D β H:ℝ} {Bc Bo:ℝ → ℝ} (ho:Continuous Bo) (hβ:0 ≤ β)
    (hob:∀s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb:∀s,-1 ≤ Bc s ∧ Bc s ≤ 1)
    (hright:∀s,3/4 ≤ s → Bc s ≤ 0)
    {a:M} {t:ℝ} {q:ℕ → subgradientGraph (n := n) (cTransform (modifiedDatum v α D β Bo))}
    {q₀:subgradientGraph (n := n) (cTransform (modifiedDatum v α D β Bo))}
    (J:ChartFixedPrefixLimit a (modifiedDatum v α D β Bo) G t q q₀) :
    let b:=graphBaseCoordinate a q₀.1
    let x:=(extChartAt 𝓘(ℝ,Model n) a).symm b
    let E:=TangentSpace 𝓘(ℝ,Model n) x
    let P:E:=chartFiberInverse a b (graphVelocityCoordinate a q₀.1)
    let pj:=fun i=>chartFiberInverse a b (J.pj₀ i)
    let κ:Type:={i:Fin (Module.finrank ℝ (Model n)+1) // 0 < J.w₀ i}
    ∀ e:E,‖e‖=1 → 0 < inner ℝ P e →
    Submodule.span ℝ (range (fun i:κ=>pj i-P))=Submodule.span ℝ {e} →
    ∀ c eta delta zeta a0:ℝ,0 < D → 0 < c → 0 < a0 →
    a0*D ≤ (inner ℝ P e)^2 → eta ≤ 1/128 → delta ≤ zeta → delta ≤ eta → zeta ≤ 1/16 →
    (∀s,s < 1-eta → 1 ≤ Bo s) →
    0 < modifiedExcess v α D β Bc Bo (riemannianExp x P) →
    2*(H+2)*β ≤ zeta*D → sectionOscillation u v x ((H+2)*β) ≤ (1+delta)*D →
    c ≤ Bc ((v (riemannianExp x P)-α)/D)-∑ i,J.w₀ i*Bo ((v (riemannianExp x (pj i))-α)/D) →
    let si:=fun i=>(v (riemannianExp x (pj i))-α)/D
    let mstar:=c/(12*(Module.finrank ℝ (Model n)+1:ℝ))
    let theta0:=min (mstar/2) (a0/3)
    ∃ i d,0 < J.w₀ i ∧ 0 < d ∧ pj i=P+d • e ∧ mstar ≤ J.w₀ i ∧
      c*D/(8*(Module.finrank ℝ (Model n)+1:ℝ)*(inner ℝ P e)) ≤ J.w₀ i*d ∧
      d ≤ 3*D/(2*(inner ℝ P e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧
      Bo (si i) ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/c ∧ 0 < theta0 ∧
      ∀ theta∈Icc (-theta0) 1,
        P+theta • (pj i-P)∈convexHull ℝ (activeLogs (modifiedDatum v α D β Bo) x) ∧
        (inner ℝ P e)/2 ≤ inner ℝ (P+theta • (pj i-P)) e ∧
        ‖pj i-P‖^2/(inner ℝ (P+theta • (pj i-P)) (pj i-P)) ≤ 3/a0 := by
  dsimp only
  intro e he hq hline c eta delta zeta a0 hD hc ha0 hqa heta hdelta hdeltaEta hzeta
    hleft hexcess herror hosc hparameter
  classical
  let b:=graphBaseCoordinate a q₀.1
  let x:=(extChartAt 𝓘(ℝ,Model n) a).symm b
  let P:=chartFiberInverse a b (graphVelocityCoordinate a q₀.1)
  let pj:=fun i=>chartFiberInverse a b (J.pj₀ i)
  let κ:Type:={i:Fin (Module.finrank ℝ (Model n)+1) // 0 < J.w₀ i}
  have hr:=positive_barycentric_restriction pj J.w₀ J.nonnegLimit J.totalLimit
  have hbar:∑ i:κ,J.w₀ i • pj i=P := by
    rw [hr.2.2.1]
    change ∑ i,J.w₀ i • chartFiberInverse a b (J.pj₀ i)=P
    simp only [←map_smul]
    rw [←map_sum,J.baryLimit]
  have hN:Fintype.card κ ≤ Module.finrank ℝ (Model n)+1 := by
    exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin _)
  have hparam:c ≤ Bc ((v (riemannianExp x P)-α)/D)-
      ∑ i:κ,J.w₀ i*Bo ((v (riemannianExp x (pj i))-α)/D) := by
    rw [hr.2.2.2 (fun i=>Bo ((v (riemannianExp x (pj i))-α)/D))]
    exact hparameter
  obtain ⟨i,d,hd,hpd,hm,hmom,hdmax,hsi,hsi',hcap,htheta,Htheta⟩:=
    hmtw.actual_outward_endpoint hu hv hdual ho hβ hob hcb hright hN
      (fun i:κ=>i.2) hr.2.1 hbar (fun i=>J.activeLimit i)
      he hq hline hD hc ha0 hqa heta hdelta hdeltaEta hzeta hleft hexcess herror hosc hparam
  refine ⟨i.1,d,i.2,hd,hpd,hm,hmom,hdmax,hsi,hsi',hcap,htheta,?_⟩
  intro theta htheta
  obtain ⟨hconv,hq',hratio⟩:=Htheta theta htheta
  refine ⟨convexHull_mono ?_ hconv,hq',hratio⟩
  rintro _ ⟨j,rfl⟩
  exact J.activeLimit j

end FirstOutward
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumOutward
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
section MaximumOutward
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma MaximumFamily.positive_excess
    {v:M → ℝ} {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ}
    (F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo)
    (hm:0 ≤ bminus) (hp:0 < bplus) (k:ℕ) :
    0 < modifiedExcess v α D (F.b k) Bc Bo
      (riemannianExp (F.row k).q.1.1 (F.row k).q.1.2) := by
  have h0:0 ≤ F.b k:=hm.trans (F.parameter k).1.le
  have hpen:0 ≤ parameterPenalty bplus (F.b k):=by
    unfold parameterPenalty
    positivity
  have H:=F.positive k
  rw [(F.row k).value] at H
  linarith only [H,hpen]

lemma MaximumJensenFamily.eventual_outward_oai
    {hmtw:WeakMTW (n:=n) (M:=M)} {u v:M → ℝ}
    (hu:Continuous u) {hv:Continuous v} (hdual:IsCostDualPair u v)
    {α D bminus bplus H:ℝ} {Bc Bo:ℝ → ℝ} {ho:Continuous Bo}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo}
    (hm:0 ≤ bminus) (hp:0 < bplus) (hprofiles:∀s,Bc s ≤ Bo s)
    (hob:∀s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb:∀s,-1 ≤ Bc s ∧ Bc s ≤ 1)
    (hright:∀s,3/4 ≤ s → Bc s ≤ 0)
    {a c:M} {N:Set (Model n)} (J:MaximumJensenFamily hmtw hv ho F a c N)
    {q:Model n} (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {A C:ℝ} (hA:0 < A) (hC:C < 0)
    (hH:∀ ε:ℝ,0 < ε → ∀ᶠ k in atTop,∀d:Model n,
      A*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
        C*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤ (J.first k).H d d)
    {eta delta zeta a0:ℝ} (hD:0 < D) (ha0:0 < a0) (hqa:2*(-C)*a0*D ≤ A)
    (heta:eta ≤ 1/128) (hdelta:delta ≤ zeta) (hdeltaEta:delta ≤ eta) (hzeta:zeta ≤ 1/16)
    (hleft:∀s,s < 1-eta → 1 ≤ Bo s)
    (herror:∀k,2*(H+2)*F.b k ≤ zeta*D)
    (hosc:∀k,sectionOscillation u v (F.row k).q.1.1 ((H+2)*F.b k) ≤ (1+delta)*D) :
    ∀ᶠ k in atTop,
      let b:=graphBaseCoordinate a (F.row k).q.1
      let x:=(extChartAt 𝓘(ℝ,Model n) a).symm b
      let P:=chartFiberInverse a b (graphVelocityCoordinate a (F.row k).q.1)
      let si:=fun i=>(v (riemannianExp x (chartFiberInverse a b ((J.first k).pj₀ i)))-α)/D
      ∃e:TangentSpace 𝓘(ℝ,Model n) x,∃i:Fin (Module.finrank ℝ (Model n)+1),∃d:ℝ,
        ‖e‖=1 ∧ 0 < inner ℝ P e ∧ a0*D ≤ (inner ℝ P e)^2 ∧ 0 < d ∧
        chartFiberInverse a b ((J.first k).pj₀ i)=P+d • e ∧
        (1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ)) ≤ (J.first k).w₀ i ∧
        (1/4096)*D/(8*(Module.finrank ℝ (Model n)+1:ℝ)*(inner ℝ P e)) ≤ (J.first k).w₀ i*d ∧
        d ≤ 3*D/(2*(inner ℝ P e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧
        Bo (si i) ≤ 12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096) := by
  have HR:=J.eventual_rank_of_center_lower hm hp hprofiles hQ hA hH
  filter_upwards [HR] with k hk
  dsimp only at hk ⊢
  obtain ⟨e,hes,he,hpe,hline,hgain⟩:=hk
  have hqa':a0*D ≤ (inner ℝ
      (chartFiberInverse a (graphBaseCoordinate a (F.row k).q.1)
        (graphVelocityCoordinate a (F.row k).q.1)) e)^2:=by
    apply (mul_le_mul_iff_right₀ (neg_pos.mpr hC)).mp
    nlinarith only [hgain,hqa]
  have hbt:graphBaseCoordinate a (F.row k).q.1∈(extChartAt 𝓘(ℝ,Model n) a).target:=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (J.poleSource k)
  have hrec:=graph_coordinate_reconstruction (J.poleSource k)
  have hx: (extChartAt 𝓘(ℝ,Model n) a).symm (graphBaseCoordinate a (F.row k).q.1)=
      (F.row k).q.1.1:=congrArg Bundle.TotalSpace.proj hrec
  have hept:riemannianExp
      ((extChartAt 𝓘(ℝ,Model n) a).symm (graphBaseCoordinate a (F.row k).q.1))
      (chartFiberInverse a (graphBaseCoordinate a (F.row k).q.1)
        (graphVelocityCoordinate a (F.row k).q.1))=
      riemannianExp (F.row k).q.1.1 (F.row k).q.1.2:=
    congrArg (fun z:TangentBundle 𝓘(ℝ,Model n) M=>riemannianExp z.1 z.2) hrec
  have hb:0 ≤ F.b k:=hm.trans (F.parameter k).1.le
  have hparam:=(F.row k).chart_first_limit_parameter (J.poleSource k) (J.first k)
  dsimp only at hparam
  simp only [movingNormal_eq hbt] at hparam
  have hpn:(1:ℝ)/4096 ≤ (1:ℝ)/4096+4*F.b k/bplus:=
    le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num) hb) hp.le)
  obtain ⟨i,d,_,hd,hpd,hmi,hmom,hdmax,hsi,hsi',hcap,_,_⟩:=
    (J.first k).outward_endpoint hmtw hu hv hdual ho hb hob hcb hright e he hpe hline
      (1/4096) eta delta zeta a0 hD (by norm_num) ha0 hqa' heta hdelta hdeltaEta hzeta hleft
      (by rw [hept]; exact F.positive_excess hm hp k) (herror k)
      (by rw [hx]; exact hosc k) (hpn.trans hparam)
  exact ⟨e,i,d,he,hpe,hqa',hd,hpd,hmi,hmom,hdmax,hsi,hsi',hcap⟩

end MaximumOutward
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.MaximumJensenFamily.eventual_outward_oai.{u_1} := @OAI.WeakMTWTransport.MaximumJensenFamily.eventual_outward_oai.{u_1}
