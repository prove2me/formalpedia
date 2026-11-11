-- Prove2me | solution 1 for OAI.WeakMTWTransport.MaximumDiagonal.center_phase_compact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:42:17.157196+00:00
-- url     : https://prove2.me/submissions/f7b1e78b-68de-48a4-8bb7-128c3dc58b82

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_LocalMetricCharts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Bundle Bornology Set MeasureTheory Manifold Filter Metric
open scoped ENNReal NNReal ContDiff Topology

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]
local notation "𝒥" => 𝓘(ℝ,E)

lemma exists_lipschitzOn_inverse_chart (x : M) :
    ∃ C : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      ball (extChartAt 𝓘(ℝ,E) x x) r ⊆ (extChartAt 𝓘(ℝ,E) x).target ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ,E) x).symm
        (ball (extChartAt 𝓘(ℝ,E) x x) r) := by
  let (y : E) : ENorm (TangentSpace 𝒥 y →L[ℝ]
      TangentSpace 𝒥 ((extChartAt 𝒥 x).symm y)) :=
    inferInstanceAs (ENorm (E →L[ℝ] TangentSpace 𝒥 ((extChartAt 𝒥 x).symm y)))
  obtain ⟨C,hCpos,hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt 𝒥 x
  obtain ⟨r,hrpos,hr⟩ : ∃ r > 0,
      ball (extChartAt 𝒥 x x) r ⊆ (extChartAt 𝒥 x).target ∩
        {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)} := by
    have hh := inter_mem (extChartAt_target_mem_nhdsWithin (I := 𝒥) x) hC
    have hh' : (extChartAt 𝒥 x).target ∩
        {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)} ∈
        𝓝 (extChartAt 𝒥 x x) := by
      simp only [ModelWithCorners.range_eq_univ, nhdsWithin_univ] at hh ⊢
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      rfl
    exact Metric.mem_nhds_iff.mp hh'
  refine ⟨C,r,hrpos,fun y hy => (hr hy).1,?_⟩
  intro u hu v hv
  let η := ContinuousAffineMap.lineMap (R := ℝ) u v
  let γ := (extChartAt 𝒥 x).symm ∘ η
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt 𝒥 x).target ∩
      {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)}) := by
    simp only [← image_subset_iff,ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap,η]
    exact ((convex_ball _ _).segment_subset hu hv).trans hr
  simp only [preimage_inter,subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hh : riemannianEDist 𝒥 ((extChartAt 𝒥 x).symm u) ((extChartAt 𝒥 x).symm v) ≤
      pathELength 𝒥 γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
  rw [IsRiemannianManifold.out (I := 𝒥)]
  apply hh.trans
  rw [← lintegral_fderiv_lineMap_eq_edist,pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have hd : mfderiv[Icc 0 1] γ t =
      (mfderiv[range 𝒥] (extChartAt 𝒥 x).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hd1 : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[range 𝒥] (extChartAt 𝒥 x).symm (η t)) (mfderiv[Icc 0 1] η t 1) :=
    congr($hd 1)
  rw [hd1]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_PoleCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma hopfLax_lipschitz {u : M → ℝ} (hu : Continuous u) {D : ℝ≥0}
    (hD : ∀ x y : M, dist x y≤D) {t : ℝ} (ht : 0<t) :
    LipschitzWith (D/Real.toNNReal t) (hopfLax t u) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [hopfLax_eq_neg_transform hu ht,hopfLax_eq_neg_transform hu ht,
    Real.dist_eq,←sub_div,abs_div,neg_sub_neg,abs_sub_comm,abs_of_pos ht]
  have H := (cTransform_lipschitz (v := fun x => t*u x) (continuous_const.mul hu) hD).dist_le_mul x y
  rw [Real.dist_eq] at H
  calc
    _ ≤ (D:ℝ)*dist x y/t := div_le_div_of_nonneg_right H ht.le
    _ = _ := by rw [NNReal.coe_div,Real.coe_toNNReal _ ht.le]; ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_HopfGradientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_chart_hopf_gradient_bound (c:M) :
    ∃K≥0,∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ,Model n) c c),∀t:ℝ,1/2 ≤ t →
      ∀u:M → ℝ,Continuous u →
      ‖fderiv ℝ (fun w=>hopfLax t u ((extChartAt 𝓘(ℝ,Model n) c).symm w)) z‖ ≤ K := by
  let : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨L,r,hr,hT,hL⟩ := exists_lipschitzOn_inverse_chart (E := Model n) c
  let D:ℝ≥0:=Real.toNNReal (Metric.diam (univ:Set M))
  have hD:∀x y:M,dist x y ≤ D := by
    intro x y
    rw [Real.coe_toNNReal _ Metric.diam_nonneg]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  refine ⟨2*(D:ℝ)*L,by positivity,?_⟩
  filter_upwards [ball_mem_nhds (extChartAt 𝓘(ℝ,Model n) c c) hr] with z hz
  intro t ht u hu
  have ht0:0 < t := by linarith
  have hn:=norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hz)
    ((hopfLax_lipschitz hu hD ht0).comp_lipschitzOnWith hL)
  have hdiv:(D:ℝ)/t ≤ 2*D := (div_le_iff₀ ht0).mpr (by nlinarith [D.coe_nonneg])
  calc
    _ ≤ ↑((D/Real.toNNReal t)*L:ℝ≥0) := hn
    _ = (D:ℝ)/t*L := by rw [NNReal.coe_mul,NNReal.coe_div,Real.coe_toNNReal _ ht0.le]
    _ ≤ _ := mul_le_mul_of_nonneg_right hdiv L.coe_nonneg

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ShortEnvelopeSemibound
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

lemma second_fderiv_comp_at {f : F → ℝ} {g : E → F} {x : E}
    (hnear : ∀ᶠ y in 𝓝 (g x),DifferentiableAt ℝ f y)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (g x))
    (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f (g a))) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)+
        fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 := hf.hasFDerivAt.comp (f := g) x hgd
  have hd2 := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hd := hd1.clm_comp hd2
  have heq : (fun a => (fderiv ℝ f (g a)).comp (fderiv ℝ g a)) =ᶠ[𝓝 x]
      fderiv ℝ (fun a => f (g a)) := by
    filter_upwards [hgd.continuousAt.eventually hnear,hg.eventually (by norm_num)]
      with a hfa hga
    exact (hfa.hasFDerivAt.comp (f := g) a
      (hga.differentiableAt (by norm_num)).hasFDerivAt).fderiv.symm
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w)
    (hd.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [Function.comp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,add_apply,add_comm] using H

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

end JointMovingPrefix
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_MovingCenterSemibound
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

end MovingCenterSemibound
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_DualCompact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section DualCompact
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] OAI.WeakMTWTransport.dualCompactGroup
attribute [local instance] OAI.WeakMTWTransport.dualCompactSpace
lemma exists_dual_limit [FiniteDimensional ℝ E]
    {gj:ℕ → E →L[ℝ] ℝ} {C:ℝ}
    (hb:∀ᶠ j in atTop,‖gj j‖≤C) :
    ∃g:E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧ Tendsto (gj ∘ σ) atTop (𝓝 g) := by
  let : FiniteDimensional ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
  obtain ⟨N,hN⟩:=eventually_atTop.mp hb
  have H : IsCompact (Metric.closedBall (0:E →L[ℝ] ℝ) C) := isCompact_closedBall _ _
  obtain ⟨g,hg,σ,hσ,hlim⟩:=H.tendsto_subseq (x := fun j => gj (j+N)) (fun j=>by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hN (j+N) (Nat.le_add_left _ _))
  exact ⟨g,fun j=>σ j+N,fun i j hij=>Nat.add_lt_add_right (hσ hij) N,hlim⟩
end DualCompact
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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_EigenOrder
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
  [CompleteSpace E]

lemma bilinearOperator_symmetric {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ v w:E, B v w=B w v) : (bilinearOperator B).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (bilinearOperator B v) w=inner ℝ v (bilinearOperator B w)
  calc
    _=B v w := bilinearOperator_inner B v w
    _=B w v := hB v w
    _=inner ℝ (bilinearOperator B w) v := (bilinearOperator_inner B w v).symm
    _=inner ℝ v (bilinearOperator B w) := real_inner_comm _ _

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearCompact
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
section BilinearCompact
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma symmetric_bilinear_norm_bound {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:∀d e,B d e=B e d) {C:ℝ} (hC:0≤C)
    (hbound:∀d,|B d d|≤C*‖d‖^2) : ‖B‖≤C := by
  let T:=bilinearOperator B
  have hT:T.IsSymmetric := bilinearOperator_symmetric hB
  have hn:‖T‖≤C := by
    rw [T.norm_eq_iSup_rayleighQuotient hT]
    apply ciSup_le
    intro d
    by_cases hd:d=0
    · simpa [hd,ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply] using hC
    · have hp:0<‖d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
      simp only [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply]
      simp only [T,bilinearOperator_inner,RCLike.re_to_real]
      rw [abs_div,abs_of_pos hp]
      apply (div_le_iff₀ hp).mpr
      exact hbound d
  apply B.opNorm_le_bound hC
  intro d
  apply (B d).opNorm_le_bound (mul_nonneg hC (norm_nonneg d))
  intro e
  calc
    ‖B d e‖ = ‖inner ℝ (T d) e‖ := by simp only [T,bilinearOperator_inner]
    _ ≤ ‖T d‖*‖e‖ := norm_inner_le_norm _ _
    _ ≤ (‖T‖*‖d‖)*‖e‖ := mul_le_mul_of_nonneg_right (T.le_opNorm d) (norm_nonneg e)
    _ ≤ (C*‖d‖)*‖e‖ := by gcongr

lemma symmetric_bilinear_norm_of_two_bounds {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:∀d e,B d e=B e d) {C D:ℝ} (hC:0≤C) (hD:0≤D)
    (hlo:∀d,-C*‖d‖^2≤B d d) (hhi:∀d,B d d≤D*‖d‖^2) : ‖B‖≤C+D := by
  apply symmetric_bilinear_norm_bound hB (add_nonneg hC hD)
  intro d
  rw [abs_le]
  constructor
  · nlinarith only [hlo d,mul_nonneg hD (sq_nonneg ‖d‖)]
  · nlinarith only [hhi d,mul_nonneg hC (sq_nonneg ‖d‖)]

omit [CompleteSpace E] in
lemma rough_hessian_symmetric {f:E → ℝ} {x:E}
    (hnear:∀ᶠ z in 𝓝 x,DifferentiableAt ℝ f z)
    (hf:DifferentiableAt ℝ (fderiv ℝ f) x) :
    ∀d e,fderiv ℝ (fderiv ℝ f) x d e=fderiv ℝ (fderiv ℝ f) x e d :=
  second_derivative_symmetric_of_eventually (hnear.mono (fun _ h=>h.hasFDerivAt)) hf.hasFDerivAt

attribute [local instance] OAI.WeakMTWTransport.bilinearCompactDualGroup
attribute [local instance] OAI.WeakMTWTransport.bilinearCompactDualSpace
attribute [local instance] OAI.WeakMTWTransport.bilinearCompactGroup
attribute [local instance] OAI.WeakMTWTransport.bilinearCompactSpace
omit [CompleteSpace E] in
lemma exists_bilinear_limit [FiniteDimensional ℝ E]
    {Bj:ℕ → E →L[ℝ] E →L[ℝ] ℝ} {C:ℝ}
    (hb:∀ᶠ j in atTop,‖Bj j‖≤C) :
    ∃B:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧ Tendsto (Bj ∘ σ) atTop (𝓝 B) := by
  let : FiniteDimensional ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
  let : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
  obtain ⟨N,hN⟩:=eventually_atTop.mp hb
  have H : IsCompact (Metric.closedBall (0:E →L[ℝ] E →L[ℝ] ℝ) C) := isCompact_closedBall _ _
  obtain ⟨B,hB,σ,hσ,hlim⟩:=H.tendsto_subseq (x := fun j => Bj (j+N)) (fun j=>by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hN (j+N) (Nat.le_add_left _ _))
  exact ⟨B,fun j=>σ j+N,fun i j hij=>Nat.add_lt_add_right (hσ hij) N,hlim⟩
end BilinearCompact
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_HessianUpperTransfer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section HessianUpperTransfer
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bilinear_bound_abs (B:E →L[ℝ] E →L[ℝ] ℝ) (d:E) :
    |B d d| ≤ ‖B‖*‖d‖^2 := by
  calc
    _ = ‖B d d‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖B d‖*‖d‖ := (B d).le_opNorm d
    _ ≤ (‖B‖*‖d‖)*‖d‖ := mul_le_mul_of_nonneg_right (B.le_opNorm d) (norm_nonneg d)
    _ = _ := by ring

lemma quadratic_upper_transfer
    {A R:E →L[ℝ] E} (hR:∀w,A (R w)=w)
    {H B E0:E →L[ℝ] E →L[ℝ] ℝ} {Q:E →L[ℝ] E →L[ℝ] E} {p:E →L[ℝ] ℝ}
    (he:∀d,B d d=E0 d d+H (A d) (A d)+p (Q d d))
    {C:ℝ} (hC:0 ≤ C) (hB:∀d,B d d ≤ C*‖d‖^2) :
    ∀w,H w w ≤ (C+‖E0‖+‖p‖*‖Q‖)*‖R‖^2*‖w‖^2 := by
  intro w
  let d:=R w
  have hE:=bilinear_bound_abs E0 d
  have hQ:|p (Q d d)| ≤ ‖p‖*‖Q‖*‖d‖^2 := by
    calc
      _ = ‖p (Q d d)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖p‖*‖Q d d‖ := p.le_opNorm _
      _ ≤ ‖p‖*(‖Q d‖*‖d‖) := mul_le_mul_of_nonneg_left ((Q d).le_opNorm d) (norm_nonneg _)
      _ ≤ ‖p‖*((‖Q‖*‖d‖)*‖d‖) := by gcongr; exact Q.le_opNorm d
      _ = _ := by ring
  have HB:=hB d
  rw [he] at HB
  rw [show A d=w from hR w] at HB
  have hh:H w w ≤ (C+‖E0‖+‖p‖*‖Q‖)*‖d‖^2 := by
    nlinarith only [HB,(abs_le.mp hE).1,(abs_le.mp hQ).1]
  calc
    _ ≤ (C+‖E0‖+‖p‖*‖Q‖)*‖d‖^2 := hh
    _ ≤ (C+‖E0‖+‖p‖*‖Q‖)*(‖R‖*‖w‖)^2 := by
      gcongr
      exact R.le_opNorm w
    _ = _ := by ring

lemma eventually_bounded_right_inverse [CompleteSpace E] [FiniteDimensional ℝ E]
    {Aj:ℕ → E →L[ℝ] E} {A:E →L[ℝ] E}
    (hA:Function.Injective A) (hlim:Tendsto Aj atTop (𝓝 A)) :
    ∃K≥0,∀ᶠ i in atTop,∃R:E →L[ℝ] E,(∀w,Aj i (R w)=w) ∧ ‖R‖ ≤ K := by
  have hu:IsUnit A := ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hA,(LinearMap.injective_iff_surjective).mp hA⟩
  obtain ⟨u,hu⟩:=hu
  subst A
  have hi:Tendsto (fun i=>Ring.inverse (Aj i)) atTop (𝓝 (Ring.inverse (u:E →L[ℝ] E))) :=
    (NormedRing.inverse_continuousAt u).tendsto.comp hlim
  have hbound:=hi.norm.eventually (gt_mem_nhds (lt_add_one ‖Ring.inverse (u:E →L[ℝ] E)‖))
  have hunit:=hlim.eventually (Units.isOpen.mem_nhds u.isUnit)
  refine ⟨‖Ring.inverse (u:E →L[ℝ] E)‖+1,by positivity,?_⟩
  filter_upwards [hbound,hunit] with i hbi hui
  refine ⟨Ring.inverse (Aj i),?_,hbi.le⟩
  intro w
  exact congrArg (fun B:E →L[ℝ] E=>B w) (Ring.mul_inverse_cancel (Aj i) hui)

end HessianUpperTransfer
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_HessianSequentialUpper
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section HessianSequentialUpper
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma sequential_quadratic_upper_transfer
    {Aj:ℕ → E →L[ℝ] E} {A:E →L[ℝ] E}
    (hA:Function.Injective A) (hAlim:Tendsto Aj atTop (𝓝 A))
    {Hj Bj Ej:ℕ → E →L[ℝ] E →L[ℝ] ℝ}
    {Qj:ℕ → E →L[ℝ] E →L[ℝ] E} {pj:ℕ → E →L[ℝ] ℝ}
    {E0:E →L[ℝ] E →L[ℝ] ℝ} {Q:E →L[ℝ] E →L[ℝ] E}
    (hElim:Tendsto Ej atTop (𝓝 E0)) (hQlim:Tendsto Qj atTop (𝓝 Q))
    (he:∀ᶠ i in atTop,∀d,Bj i d d=Ej i d d+Hj i (Aj i d) (Aj i d)+pj i (Qj i d d))
    {P C:ℝ} (hP:0 ≤ P) (hC:0 ≤ C)
    (hp:∀ᶠ i in atTop,‖pj i‖ ≤ P)
    (hB:∀ᶠ i in atTop,∀d,Bj i d d ≤ C*‖d‖^2) :
    ∃K≥0,∀ᶠ i in atTop,∀d,Hj i d d ≤ K*‖d‖^2 := by
  obtain ⟨R,hR,HR⟩:=eventually_bounded_right_inverse hA hAlim
  have HE : ∀ᶠ i in atTop, ‖Ej i‖ < ‖E0‖+1 := ((continuous_norm.tendsto E0).comp hElim).eventually (gt_mem_nhds (lt_add_one ‖E0‖))
  have HQ : ∀ᶠ i in atTop, ‖Qj i‖ < ‖Q‖+1 := ((continuous_norm.tendsto Q).comp hQlim).eventually (gt_mem_nhds (lt_add_one ‖Q‖))
  refine ⟨(C+(‖E0‖+1)+P*(‖Q‖+1))*R^2,by positivity,?_⟩
  filter_upwards [HR,HE,HQ,he,hp,hB] with i hi hei hqi heqi hpi hbi
  obtain ⟨r,hr,hri⟩:=hi
  intro w
  apply (quadratic_upper_transfer hr heqi hC hbi w).trans
  gcongr

end HessianSequentialUpper
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_Diagonal
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

lemma diagonal_tendsto_of_close {X : Type*} [PseudoMetricSpace X]
    {f a : ℕ → X} {x : X} {ε : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 x)) (hε : Tendsto ε atTop (𝓝 0))
    (hclose : ∀ᶠ k in atTop,dist (f k) (a k)≤ε k) : Tendsto f atTop (𝓝 x) := by
  apply tendsto_of_tendsto_of_dist ha
  exact squeeze_zero' (Eventually.of_forall (fun _=>dist_nonneg)) (hclose.mono (fun k hk=>by simpa only [dist_comm] using hk)) hε

end WeakMTWTransport

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

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

lemma MaximumDiagonal.limits (J : MaximumJensenFamily hmtw hv ho F a c N)
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    (hε : Tendsto ε atTop (𝓝 0)) {q : Model n}
    (hQ : Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M))) (hc : riemannianExp a q=c) :
    Tendsto (fun k=>graphBaseCoordinate a (J.samplePoint k (S.ν k)).1) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) ∧
    Tendsto (fun k=>graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1) atTop (𝓝 q) ∧
    Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) ∧
    Tendsto (fun k=>J.sampleGradient k (S.ν k)) atTop (𝓝 0) := by
  obtain ⟨hb,hp,hz,hy⟩ := F.limit_coordinates hQ
  rw [hc] at hy
  have hY := ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds
    (mem_extChartAt_source (I := 𝓘(ℝ,Model n)) c))).tendsto.comp hy
  refine ⟨diagonal_tendsto_of_close hb hε (Eventually.of_forall (fun k=>(S.baseClose k).le)),
    diagonal_tendsto_of_close hp hε (Eventually.of_forall (fun k=>(S.velocityClose k).le)),
    diagonal_tendsto_of_close hY hε (Eventually.of_forall (fun k=>(S.centerClose k).le)),?_⟩
  apply diagonal_tendsto_of_close tendsto_const_nhds hε
  exact Eventually.of_forall (fun k=>by simpa only [dist_zero_right] using (S.gradientClose k).le)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumEndpoint
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
section MaximumEndpoint
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.movingChart {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P) (k:ℕ) :
    movingPrefixChart a c (F.t k) (graphBaseCoordinate a (J.samplePoint k (S.ν k)).1)
      (graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1)=
        (J.sample k).z (J.sampleIndex k (S.ν k)) := by
  rw [movingPrefixChart,movingPrefix_graph_coordinates (S.poleSource k)]
  exact S.endpointChart k

lemma MaximumDiagonal.endpoint_tendsto {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    {q:Model n} (hc:riemannianExp a q=c)
    (hb:Tendsto (fun k=>graphBaseCoordinate a (J.samplePoint k (S.ν k)).1) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hp:Tendsto (fun k=>graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1) atTop (𝓝 q)) :
    Tendsto (fun k=>(J.sample k).z (J.sampleIndex k (S.ν k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) := by
  have hb0:extChartAt 𝓘(ℝ,Model n) a a∈(extChartAt 𝓘(ℝ,Model n) a).target:=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hgc:movingPrefix a 1 (extChartAt 𝓘(ℝ,Model n) a a) q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    rw [movingPrefix_at_center,one_smul,hc]
    exact mem_extChartAt_source c
  have H:=((joint_movingPrefixChart_contDiffAt hb0 hgc).continuousAt.tendsto).comp
    ((F.time.prodMk_nhds hb).prodMk_nhds hp)
  change Tendsto (fun k=>movingPrefixChart a c (F.t k)
    (graphBaseCoordinate a (J.samplePoint k (S.ν k)).1)
    (graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1)) atTop
    (𝓝 (movingPrefixChart a c 1 (extChartAt 𝓘(ℝ,Model n) a a) q)) at H
  simp only [S.movingChart] at H
  simpa only [movingPrefixChart,movingPrefix_at_center,one_smul,hc] using H

end MaximumEndpoint
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MovingCenterUpper
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
section MovingCenterUpper
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma coordinateCenterMatrix_chain {a c:M} {t:ℝ} {b p:Model n} {G:M → ℝ}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc:movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hn:∀ᶠ z in 𝓝 (movingPrefixChart a c t b p),
      DifferentiableAt ℝ (fun w=>G ((extChartAt 𝓘(ℝ,Model n) c).symm w)) z)
    (hd:DifferentiableAt ℝ (fderiv ℝ (fun w=>G ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
      (movingPrefixChart a c t b p)) (d:Model n) :
    coordinateCenterMatrix a t G b p d d=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p d d+
      fderiv ℝ (fderiv ℝ (fun w=>G ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (movingPrefixChart a c t b p) (fderiv ℝ (movingPrefixChart a c t b) p d)
          (fderiv ℝ (movingPrefixChart a c t b) p d)+
      fderiv ℝ (fun w=>G ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (movingPrefixChart a c t b p) (fderiv ℝ (fderiv ℝ (movingPrefixChart a c t b)) p d d) := by
  rw [coordinateCenterMatrix_chart hb hc]
  simp only [add_apply]
  have hg:ContDiffAt ℝ 2 (movingPrefixChart a c t b) p :=
    ((joint_movingPrefixChart_contDiffAt hb hc).comp p
      (contDiffAt_const.prodMk contDiffAt_id)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [second_fderiv_comp_at hn hd hg]
  exact (add_assoc _ _ _).symm

lemma movingPrefixChart_injective_at_center {a c:M} {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (hc:riemannianExp a q=c) :
    Function.Injective (fderiv ℝ (movingPrefixChart a c 1 (extChartAt 𝓘(ℝ,Model n) a a)) q) := by
  have heq:movingPrefixChart a c 1 (extChartAt 𝓘(ℝ,Model n) a a)=
      (fun r:Model n=>extChartAt 𝓘(ℝ,Model n) (riemannianExp a q) (riemannianExp a r)) := by
    funext r
    simp only [movingPrefixChart,movingPrefix_at_center,one_smul,hc]
  rw [heq]
  exact riemannianExp_interior_nonconjugate hq

lemma moving_center_derivative_limits {a c:M} {q:Model n}
    (hc:riemannianExp a q=c) {bj qj:ℕ → Model n} {tj:ℕ → ℝ}
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq:Tendsto qj atTop (𝓝 q)) (ht:Tendsto tj atTop (𝓝 1)) :
    Tendsto (fun i=>fderiv ℝ (movingPrefixChart a c (tj i) (bj i)) (qj i)) atTop
      (𝓝 (fderiv ℝ (movingPrefixChart a c 1 (extChartAt 𝓘(ℝ,Model n) a a)) q)) ∧
    Tendsto (fun i=>fderiv ℝ (fderiv ℝ (movingPrefixChart a c (tj i) (bj i))) (qj i)) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ (movingPrefixChart a c 1 (extChartAt 𝓘(ℝ,Model n) a a))) q)) := by
  let b:=extChartAt 𝓘(ℝ,Model n) a a
  let g:(ℝ×Model n) → Model n → Model n:=fun z r=>movingPrefixChart a c z.1 z.2 r
  have hb0:b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hgc:movingPrefix a 1 b q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    simp only [b,movingPrefix_at_center,one_smul,hc]
    exact mem_extChartAt_source c
  have hg:ContDiffAt ℝ ∞ (Function.uncurry g) ((1,b),q):=
    joint_movingPrefixChart_contDiffAt (a := a) (c := c) (t := 1) (b := b) (p := q) hb0 hgc
  have harg:Tendsto (fun i=>((tj i,bj i),qj i)) atTop (𝓝 ((1,b),q)):=
    (ht.prodMk_nhds hb).prodMk_nhds hqq
  have hA : ContinuousAt (fun z:(ℝ×Model n)×Model n=>fderiv ℝ (g z.1) z.2) ((1,b),q) :=
    (ContDiffAt.partial_snd_fderiv (f := g) (q := (1,b)) (h := q) hg).continuousAt
  have hQ : ContinuousAt (fun z:(ℝ×Model n)×Model n=>fderiv ℝ (fderiv ℝ (g z.1)) z.2) ((1,b),q) :=
    (ContDiffAt.partial_snd_fderiv_two (f := g) (q := (1,b)) (h := q) hg).continuousAt
  have H1:=hA.tendsto.comp harg
  have H2:=hQ.tendsto.comp harg
  dsimp only [Function.comp_def,g,b] at H1 H2
  exact ⟨H1,H2⟩

lemma moving_center_limit_data {a c:M} {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (hc:riemannianExp a q=c) {bj qj:ℕ → Model n} {tj:ℕ → ℝ}
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq:Tendsto qj atTop (𝓝 q)) (ht:Tendsto tj atTop (𝓝 1)) :
    let g:(ℝ×Model n) → Model n → Model n:=fun z r=>movingPrefixChart a c z.1 z.2 r
    let b:=extChartAt 𝓘(ℝ,Model n) a a
    Function.Injective (fderiv ℝ (g (1,b)) q) ∧
    Tendsto (fun i=>fderiv ℝ (g (tj i,bj i)) (qj i)) atTop (𝓝 (fderiv ℝ (g (1,b)) q)) ∧
    Tendsto (fun i=>fderiv ℝ (fderiv ℝ (g (tj i,bj i))) (qj i)) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ (g (1,b))) q)) ∧
    Tendsto (fun i=>fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i)) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 b)) q)) ∧
    (∀ᶠ i in atTop,bj i∈(extChartAt 𝓘(ℝ,Model n) a).target) ∧
    (∀ᶠ i in atTop,movingPrefix a (tj i) (bj i) (qj i)∈(extChartAt 𝓘(ℝ,Model n) c).source) := by
  dsimp only
  let b:=extChartAt 𝓘(ℝ,Model n) a a
  let g:(ℝ×Model n) → Model n → Model n:=fun z r=>movingPrefixChart a c z.1 z.2 r
  have hb0:b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hgc:movingPrefix a 1 b q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    simp only [b,movingPrefix_at_center,one_smul,hc]
    exact mem_extChartAt_source c
  have harg:Tendsto (fun i=>((tj i,bj i),qj i)) atTop (𝓝 ((1,b),q)):=
    (ht.prodMk_nhds hb).prodMk_nhds hqq
  have hA:Function.Injective (fderiv ℝ (g (1,b)) q) :=
    movingPrefixChart_injective_at_center hq hc
  obtain ⟨hAlim,hQlim⟩ := moving_center_derivative_limits hc hb hqq ht
  have hElim:=moving_energy_hessian_tendsto (a := a) hq hb hqq ht
  have hbt:∀ᶠ i in atTop,bj i∈(extChartAt 𝓘(ℝ,Model n) a).target:=
    hb.eventually ((isOpen_extChartAt_target a).mem_nhds hb0)
  have hct:∀ᶠ i in atTop,movingPrefix a (tj i) (bj i) (qj i)∈(extChartAt 𝓘(ℝ,Model n) c).source:=
    ((joint_movingPrefix_contMDiffAt (a := a) (t := 1) (b := b) (p := q) hb0).continuousAt.tendsto.comp harg).eventually
      ((isOpen_extChartAt_source c).mem_nhds hgc)
  exact ⟨hA,hAlim,hQlim,hElim,hbt,hct⟩

lemma moving_center_sequential_upper {a c:M} {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (hc:riemannianExp a q=c) {bj qj:ℕ → Model n} {tj:ℕ → ℝ}
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq:Tendsto qj atTop (𝓝 q)) (ht:Tendsto tj atTop (𝓝 1))
    {Gj:ℕ → M → ℝ}
    (hnear:∀ᶠ i in atTop,∀ᶠ z in 𝓝 (movingPrefixChart a c (tj i) (bj i) (qj i)),
      DifferentiableAt ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)) z)
    (hder:∀ᶠ i in atTop,DifferentiableAt ℝ
      (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (movingPrefixChart a c (tj i) (bj i) (qj i)))
    {P C:ℝ} (hP:0 ≤ P) (hC:0 ≤ C)
    (hp:∀ᶠ i in atTop,‖fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
      (movingPrefixChart a c (tj i) (bj i) (qj i))‖ ≤ P)
    (hB:∀ᶠ i in atTop,∀d,coordinateCenterMatrix a (tj i) (Gj i) (bj i) (qj i) d d ≤ C*‖d‖^2) :
    ∃K≥0,∀ᶠ i in atTop,∀d,
      fderiv ℝ (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (movingPrefixChart a c (tj i) (bj i) (qj i)) d d ≤ K*‖d‖^2 := by
  let g:(ℝ×Model n) → Model n → Model n:=fun z r=>movingPrefixChart a c z.1 z.2 r
  obtain ⟨hA,hAlim,hQlim,hElim,hbt,hct⟩:=moving_center_limit_data hq hc hb hqq ht
  have he:∀ᶠ i in atTop,∀d,
      coordinateCenterMatrix a (tj i) (Gj i) (bj i) (qj i) d d=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i) d d+
      fderiv ℝ (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (g (tj i,bj i) (qj i)) (fderiv ℝ (g (tj i,bj i)) (qj i) d)
          (fderiv ℝ (g (tj i,bj i)) (qj i) d)+
      fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (g (tj i,bj i) (qj i)) (fderiv ℝ (fderiv ℝ (g (tj i,bj i))) (qj i) d d) := by
    filter_upwards [hbt,hct,hnear,hder] with i hbi hci hni hdi
    exact coordinateCenterMatrix_chain hbi hci hni hdi
  exact sequential_quadratic_upper_transfer hA hAlim hElim hQlim he hP hC hp hB

end MovingCenterUpper
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumCenterUpper
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
section MaximumCenterUpper
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.sample_center_upper {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {C:ℝ}
    (hL:∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ C*‖d‖^2) :
    ∀ᶠ k in atTop,∀d,J.sampleH k (S.ν k) d d ≤ (C+1)*‖d‖^2 := by
  filter_upwards [hL,hε.eventually (gt_mem_nhds zero_lt_one)] with k hk hεk
  intro d
  calc
    _ ≤ (J.first k).H d d+1*‖d‖^2 := bilinear_quadratic_close ((S.HClose k).le.trans hεk.le) d
    _ ≤ (J.first k).L d d+1*‖d‖^2 := by linarith only [(J.first k).upper d]
    _ ≤ C*‖d‖^2+1*‖d‖^2 := by linarith only [hk d]
    _ = _ := by ring

lemma MaximumDiagonal.center_gradient_bound {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hg:Tendsto (fun k=>J.sampleGradient k (S.ν k)) atTop (𝓝 0))
    (hz:Tendsto (fun k=>(J.sample k).z (J.sampleIndex k (S.ν k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c))) :
    ∃K≥0,∀ᶠ k in atTop,
      ‖fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
        ((J.sample k).z (J.sampleIndex k (S.ν k)))‖ ≤ K := by
  obtain ⟨K,hK,HK⟩:=exists_chart_hopf_gradient_bound (n := n) c
  have hgg:∀ᶠ k in atTop,‖J.sampleGradient k (S.ν k)‖<1 := by
    simpa only [norm_zero,Function.comp_def] using ((continuous_norm.tendsto (0:Model n →L[ℝ] ℝ)).comp hg).eventually
      (gt_mem_nhds (by simp : ‖(0:Model n →L[ℝ] ℝ)‖<1))
  refine ⟨1+K,by linarith,?_⟩
  filter_upwards [hz.eventually HK,F.time.eventually (lt_mem_nhds (by norm_num : (1/2:ℝ)<1)),hgg]
    with k hk htk hgk
  have houter:=hk (F.t k) htk.le (cTransform (modifiedDatum v α D (F.b k) Bo))
    (continuous_cTransform (continuous_modifiedDatum hv α D (F.b k) ho))
  let x:=(J.sample k).z (J.sampleIndex k (S.ν k))
  have he:fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c) x=
      J.sampleGradient k (S.ν k)-
        fderiv ℝ (chartOuterEnvelope (modifiedDatum v α D (F.b k) Bo) (F.t k) c) x := by
    dsimp only [MaximumJensenFamily.sampleGradient,x]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hgk.le houter)

lemma MaximumDiagonal.center_upper {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (he:riemannianExp a q=c)
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {C:ℝ} (hC:0 ≤ C) (hL:∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ C*‖d‖^2) :
    ∃K≥0,∀ᶠ k in atTop,∀d,
      fderiv ℝ (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k))) d d ≤ K*‖d‖^2 := by
  obtain ⟨hb,hp,hx,hg⟩:=S.limits J hε hQ he
  have hz:=S.endpoint_tendsto he hb hp
  obtain ⟨K,hK,HK⟩:=S.center_gradient_bound hg hz
  have hn:∀ᶠ k in atTop,∀ᶠ z in 𝓝 ((J.sample k).z (J.sampleIndex k (S.ν k))),
      DifferentiableAt ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c) z := by
    apply Eventually.of_forall
    intro k
    filter_upwards [(J.sample k).openRegion.mem_nhds ((J.sample k).sampleInRegion (J.sampleIndex k (S.ν k)))] with z hz
    exact (J.sample k).centerDifferentiable z hz
  have hd:∀ᶠ k in atTop,DifferentiableAt ℝ
      (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k))) :=
    Eventually.of_forall (fun k=>((J.sample k).samples (J.sampleIndex k (S.ν k))).2.2.2.2.2.2.2.2.1)
  have HB:=S.sample_center_upper hε hL
  have H:=moving_center_sequential_upper hq he hb hp F.time
    (Gj := fun k=>hopfLax (1-F.t k) (modifiedDatum v α D (F.b k) Bc))
    (by simpa only [S.movingChart] using hn) (by simpa only [S.movingChart] using hd)
    hK (show 0 ≤ C+1 by linarith) (by simpa only [S.movingChart] using HK) HB
  simpa only [S.movingChart] using H

end MaximumCenterUpper
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MovingCenterLower
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
section MovingCenterLower
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma moving_center_sequential_lower {a c:M} {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (hc:riemannianExp a q=c) {bj qj:ℕ → Model n} {tj:ℕ → ℝ}
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hqq:Tendsto qj atTop (𝓝 q)) (ht:Tendsto tj atTop (𝓝 1))
    {Gj:ℕ → M → ℝ}
    (hnear:∀ᶠ i in atTop,∀ᶠ z in 𝓝 (movingPrefixChart a c (tj i) (bj i) (qj i)),
      DifferentiableAt ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)) z)
    (hder:∀ᶠ i in atTop,DifferentiableAt ℝ
      (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (movingPrefixChart a c (tj i) (bj i) (qj i)))
    {P C:ℝ} (hP:0 ≤ P) (hC:0 ≤ C)
    (hp:∀ᶠ i in atTop,‖fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
      (movingPrefixChart a c (tj i) (bj i) (qj i))‖ ≤ P)
    (hB:∀ᶠ i in atTop,∀d,-C*‖d‖^2 ≤ coordinateCenterMatrix a (tj i) (Gj i) (bj i) (qj i) d d) :
    ∃K≥0,∀ᶠ i in atTop,∀d,
      fderiv ℝ (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (movingPrefixChart a c (tj i) (bj i) (qj i)) d d ≥ -K*‖d‖^2 := by
  let g:(ℝ×Model n) → Model n → Model n:=fun z r=>movingPrefixChart a c z.1 z.2 r
  obtain ⟨hA,hAlim,hQlim,hElim,hbt,hct⟩:=moving_center_limit_data hq hc hb hqq ht
  have he:∀ᶠ i in atTop,∀d,
      coordinateCenterMatrix a (tj i) (Gj i) (bj i) (qj i) d d=
      fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i) d d+
      fderiv ℝ (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (g (tj i,bj i) (qj i)) (fderiv ℝ (g (tj i,bj i)) (qj i) d)
          (fderiv ℝ (g (tj i,bj i)) (qj i) d)+
      fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (g (tj i,bj i) (qj i)) (fderiv ℝ (fderiv ℝ (g (tj i,bj i))) (qj i) d d) := by
    filter_upwards [hbt,hct,hnear,hder] with i hbi hci hni hdi
    exact coordinateCenterMatrix_chain hbi hci hni hdi
  have heNeg:∀ᶠ i in atTop,∀d,
      (-coordinateCenterMatrix a (tj i) (Gj i) (bj i) (qj i)) d d=
      (-fderiv ℝ (fderiv ℝ (movingPrefixEnergy a (tj i) (bj i))) (qj i)) d d+
      (-fderiv ℝ (fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w)))
        (g (tj i,bj i) (qj i))) (fderiv ℝ (g (tj i,bj i)) (qj i) d)
          (fderiv ℝ (g (tj i,bj i)) (qj i) d)+
      (-fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (g (tj i,bj i) (qj i))) (fderiv ℝ (fderiv ℝ (g (tj i,bj i))) (qj i) d d) := by
    filter_upwards [he] with i hi
    intro d
    simp only [neg_apply]
    linarith only [hi d]
  have hpNeg:∀ᶠ i in atTop,‖-fderiv ℝ (fun w=>Gj i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
      (g (tj i,bj i) (qj i))‖≤P := by simpa only [norm_neg] using hp
  have hBNeg:∀ᶠ i in atTop,∀d,(-coordinateCenterMatrix a (tj i) (Gj i) (bj i) (qj i)) d d≤C*‖d‖^2 := by
    filter_upwards [hB] with i hi
    intro d
    simp only [neg_apply]
    linarith only [hi d]
  obtain ⟨K,hK,HK⟩:=sequential_quadratic_upper_transfer hA hAlim hElim.neg hQlim heNeg hP hC hpNeg hBNeg
  refine ⟨K,hK,?_⟩
  filter_upwards [HK] with i hi
  intro d
  have H:=hi d
  simp only [neg_apply] at H
  linarith only [H]

end MovingCenterLower
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumCenterCompact
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
section MaximumCenterCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

attribute [local instance] OAI.WeakMTWTransport.maximumDualGroup
attribute [local instance] OAI.WeakMTWTransport.maximumDualSpace
local instance maximumBilinearGroup_r08df3f_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumBilinearSpace_r08df3f_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma MaximumDiagonal.sample_center_lower {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {C:ℝ}
    (hH:∀ᶠ k in atTop,∀d,-C*‖d‖^2 ≤ (J.first k).H d d) :
    ∀ᶠ k in atTop,∀d,-(C+1)*‖d‖^2 ≤ J.sampleH k (S.ν k) d d := by
  filter_upwards [hH,hε.eventually (gt_mem_nhds zero_lt_one)] with k hk hεk
  intro d
  have hn : ‖(J.first k).H-J.sampleH k (S.ν k)‖ ≤ 1 := by
    rw [norm_sub_rev]
    exact (S.HClose k).le.trans hεk.le
  have hclose:=bilinear_quadratic_close hn d
  nlinarith only [hclose,hk d]

lemma MaximumDiagonal.center_lower {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (he:riemannianExp a q=c)
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {C:ℝ} (hC:0 ≤ C) (hH:∀ᶠ k in atTop,∀d,-C*‖d‖^2 ≤ (J.first k).H d d) :
    ∃K≥0,∀ᶠ k in atTop,∀d,-K*‖d‖^2 ≤
      fderiv ℝ (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k))) d d := by
  obtain ⟨hb,hp,hx,hg⟩:=S.limits J hε hQ he
  have hz:=S.endpoint_tendsto he hb hp
  obtain ⟨K,hK,HK⟩:=S.center_gradient_bound hg hz
  have hn:∀ᶠ k in atTop,∀ᶠ z in 𝓝 ((J.sample k).z (J.sampleIndex k (S.ν k))),
      DifferentiableAt ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c) z := by
    apply Eventually.of_forall
    intro k
    filter_upwards [(J.sample k).openRegion.mem_nhds ((J.sample k).sampleInRegion (J.sampleIndex k (S.ν k)))] with z hz
    exact (J.sample k).centerDifferentiable z hz
  have hd:∀ᶠ k in atTop,DifferentiableAt ℝ
      (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k))) :=
    Eventually.of_forall (fun k=>((J.sample k).samples (J.sampleIndex k (S.ν k))).2.2.2.2.2.2.2.2.1)
  have HB:=S.sample_center_lower hε hH
  have H:=moving_center_sequential_lower hq he hb hp F.time
    (Gj := fun k=>hopfLax (1-F.t k) (modifiedDatum v α D (F.b k) Bc))
    (by simpa only [S.movingChart] using hn) (by simpa only [S.movingChart] using hd)
    hK (show 0 ≤ C+1 by linarith) (by simpa only [S.movingChart] using HK) HB
  simpa only [S.movingChart] using H

lemma MaximumDiagonal.center_compact {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (he:riemannianExp a q=c)
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {C U:ℝ} (hC:0 ≤ C) (hD:0 ≤ U)
    (hH:∀ᶠ k in atTop,∀d,-C*‖d‖^2 ≤ (J.first k).H d d)
    (hL:∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ U*‖d‖^2) :
    ∃B:Model n →L[ℝ] Model n →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (fun i=>fderiv ℝ
        (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b (σ i)) Bc) (F.t (σ i)) c))
        ((J.sample (σ i)).z (J.sampleIndex (σ i) (S.ν (σ i))))) atTop (𝓝 B) := by
  obtain ⟨K,hK,HK⟩:=S.center_lower hε hq he hQ hC hH
  obtain ⟨L,hL',HL⟩:=S.center_upper hε hq he hQ hD hL
  change ∃ B σ, StrictMono σ ∧ Tendsto ((fun k => fderiv ℝ
    (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
      ((J.sample k).z (J.sampleIndex k (S.ν k)))) ∘ σ) atTop (𝓝 B)
  apply exists_bilinear_limit (C := K+L)
  filter_upwards [HK,HL] with i hi hl
  apply symmetric_bilinear_norm_of_two_bounds (C := K) (D := L) _ hK hL' hi hl
  apply rough_hessian_symmetric
  · filter_upwards [(J.sample i).openRegion.mem_nhds
      ((J.sample i).sampleInRegion (J.sampleIndex i (S.ν i)))] with z hz
    exact (J.sample i).centerDifferentiable z hz
  · exact ((J.sample i).samples (J.sampleIndex i (S.ν i))).2.2.2.2.2.2.2.2.1

end MaximumCenterCompact
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumPhaseCompact
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
section MaximumPhaseCompact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

local instance maximumPhaseDualGroup_r08df3f_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumPhaseDualSpace_r08df3f_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumPhaseBilinearGroup_r08df3f_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumPhaseBilinearSpace_r08df3f_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma MaximumDiagonal.center_phase_compact_oai {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0)) {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a)
    (he:riemannianExp a q=c)
    (hQ:Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)))
    {C U:ℝ} (hC:0 ≤ C) (hU:0 ≤ U)
    (hH:∀ᶠ k in atTop,∀d,-C*‖d‖^2 ≤ (J.first k).H d d)
    (hL:∀ᶠ k in atTop,∀d,(J.first k).L d d ≤ U*‖d‖^2) :
    ∃g:Model n →L[ℝ] ℝ,∃B:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      ∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (fun i=>fderiv ℝ
        (chartCenterEnvelope (modifiedDatum v α D (F.b (σ i)) Bc) (F.t (σ i)) c)
        ((J.sample (σ i)).z (J.sampleIndex (σ i) (S.ν (σ i))))) atTop (𝓝 g) ∧
      Tendsto (fun i=>fderiv ℝ
        (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b (σ i)) Bc) (F.t (σ i)) c))
        ((J.sample (σ i)).z (J.sampleIndex (σ i) (S.ν (σ i))))) atTop (𝓝 B) := by
  obtain ⟨B,σ,hσ,HB⟩:=S.center_compact hε hq he hQ hC hU hH hL
  obtain ⟨hb,hp,hx,hg⟩:=S.limits J hε hQ he
  have hz:=S.endpoint_tendsto he hb hp
  obtain ⟨K,hK,HK⟩:=S.center_gradient_bound hg hz
  obtain ⟨g,τ,hτ,HG⟩:=exists_dual_limit (hσ.tendsto_atTop.eventually HK)
  exact ⟨g,B,σ ∘ τ,hσ.comp hτ,HG,HB.comp hτ.tendsto_atTop⟩

end MaximumPhaseCompact
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.MaximumDiagonal.center_phase_compact_oai.{u_1} := @OAI.WeakMTWTransport.MaximumDiagonal.center_phase_compact_oai.{u_1}
