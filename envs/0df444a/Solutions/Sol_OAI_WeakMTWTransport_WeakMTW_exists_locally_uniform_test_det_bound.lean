-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.exists_locally_uniform_test_det_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:37:51.792604+00:00
-- url     : https://prove2.me/submissions/66c5f823-5f5f-4ae9-99b3-b15a44e90797

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
import Definitions.Def_OAIQ232A020
import Definitions.Def_OAIQ232A030

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MetricDefinitions
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

variable {M : Type*} [MetricSpace M]

variable [CompactSpace M] [Nonempty M]

omit [CompactSpace M] [Nonempty M] in
lemma contactGap_symm (u v : M → ℝ) (x y : M) :
    contactGap u v x y = contactGap v u y x := by
  dsimp [contactGap]
  rw [cost_symm x y]
  ring

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_RadialNull
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

section TransportCertificates
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

omit [MetricSpace M] [BorelSpace M] in
lemma density_nonnegative {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    ∀ᵐ x ∂vol, 0 ≤ rho x := by
  filter_upwards [hrho.2.2.2] with x hx
  exact hlam.le.trans hx.1

omit [MetricSpace M] [BorelSpace M] in
lemma densityMeasure_probability {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    IsProbabilityMeasure (densityMeasure vol rho) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hrho.2.1 (density_nonnegative hlam hrho),
    hrho.2.2.1, ENNReal.ofReal_one]

end TransportCertificates

open scoped BoundedContinuousFunction

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

lemma boundedCTransform_apply (v : M →ᵇ ℝ) (x : M) :
    boundedCTransform v x = cTransform v x := rfl

lemma boundedCTransform_nonexpansive : LipschitzWith 1 (boundedCTransform (M := M)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
  intro x
  rw [Real.dist_eq, abs_le]
  have hbound (a b : M →ᵇ ℝ) : cTransform a x - cTransform b x ≤ dist a b := by
    rw [sub_le_iff_le_add, cTransform_le_iff a.continuous]
    intro y
    have hg := cTransform_gap_nonneg b.continuous x y
    have hd := BoundedContinuousFunction.dist_coe_le_dist (f := a) (g := b) y
    rw [Real.dist_eq, abs_le] at hd
    dsimp [contactGap] at hg
    linarith [hd.1]
  constructor
  · have hh := hbound w v
    rw [dist_comm w v] at hh
    change -dist v w ≤ cTransform v x - cTransform w x
    linarith
  · exact hbound v w

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

omit [Nonempty M] in
lemma coordinateBackward_contMDiffAt {a : M} {q : ℝ × Model n × (Model n →L[ℝ] ℝ)}
    (hq : q.2.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,ℝ × Model n × (Model n →L[ℝ] ℝ)) 𝓘(ℝ,Model n) ∞
      (coordinateBackward a) q := by
  have hg := (contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hq)
  have hi := (riemannianCoordinateMetric_isInvertible hq).contDiffAt_map_inverse.comp q.2.1 hg
  have hz : ContDiffAt ℝ ∞ (fun q : ℝ × Model n × (Model n →L[ℝ] ℝ) => q.2.1) q :=
    contDiffAt_fst.comp q contDiffAt_snd
  have hl : ContDiffAt ℝ ∞ (fun q : ℝ × Model n × (Model n →L[ℝ] ℝ) => q.2.2) q :=
    contDiffAt_snd.comp q contDiffAt_snd
  have hv := (contDiffAt_fst.neg.smul ((hi.comp q hz).clm_apply hl))
  exact (movingNormal_contMDiffAt hq).comp q (hz.prodMk hv).contMDiffAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactDerivative
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma coordinateContact_contDiffAt {a b : M} {q : Model n × (Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hb : coordinateBackward a (-1,q.1,q.2)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    ContDiffAt ℝ ∞ (coordinateContact (n := n) a b) q := by
  have hi : ContDiffAt ℝ ∞ (fun z : Model n × (Model n →L[ℝ] ℝ) => ((-1:ℝ),z)) q :=
    contDiffAt_const.prodMk contDiffAt_id
  have hq' := (coordinateBackward_contMDiffAt (q := (-1,q.1,q.2)) hq).comp q
    hi.contMDiffAt
  have hb' : coordinateBackward a (-1,q.1,q.2)∈(chartAt (Model n) b).source := by
    simpa only [extChartAt_source] using hb
  exact ((contMDiffAt_extChartAt' hb').comp q hq').contDiffAt
end ContactDerivative
end WeakMTWTransport

end

end

end

end OAI
end

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

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] in

lemma hausdorff_nondifferentiable_chart_image_null {u : M → ℝ} {K C : ℝ≥0}
    (hu : LipschitzWith K u) (x : M) {r : ℝ}
    (hr : ball (extChartAt 𝒥 x x) r ⊆ (extChartAt 𝒥 x).target)
    (hC : LipschitzOnWith C (extChartAt 𝒥 x).symm (ball (extChartAt 𝒥 x x) r)) :
    (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure M)
      {y | y ∈ (extChartAt 𝒥 x).symm '' ball (extChartAt 𝒥 x x) r ∧
        ¬ MDifferentiableAt 𝒥 𝓘(ℝ,ℝ) u y} = 0 := by
  let B : Set E := {z | z ∈ ball (extChartAt 𝒥 x x) r ∧
    ¬ DifferentiableAt ℝ (u ∘ (extChartAt 𝒥 x).symm) z}
  have hB : (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure E) B = 0 := by
    have hh := (hu.comp_lipschitzOnWith hC).ae_differentiableWithinAt_of_mem
      (μ := (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure E))
    apply measure_mono_null _ (ae_iff.mp hh)
    intro z hz hdiff
    exact hz.2 ((hdiff hz.1).differentiableAt (isOpen_ball.mem_nhds hz.1))
  have himage : (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure M)
      ((extChartAt 𝒥 x).symm '' B) = 0 := by
    apply le_antisymm ?_ (by positivity)
    have hh := (hC.mono (show B ⊆ ball (extChartAt 𝒥 x x) r from fun _ h => h.1)).hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (by positivity)
    simpa only [hB,mul_zero] using hh
  apply measure_mono_null _ himage
  rintro y ⟨⟨z,hz,rfl⟩,hnot⟩
  refine ⟨z,⟨hz,?_⟩,rfl⟩
  intro hdiff
  apply hnot
  have hsrc : (extChartAt 𝒥 x).symm z ∈ (chartAt E x).source := by
    simpa only [extChartAt_source] using (extChartAt 𝒥 x).map_target (hr hz)
  have hD : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (u ∘ (extChartAt 𝒥 x).symm)
      ((extChartAt 𝒥 x) ((extChartAt 𝒥 x).symm z)) := by
    rw [(extChartAt 𝒥 x).right_inv (hr hz)]
    exact hdiff.mdifferentiableAt
  have hh := hD.comp ((extChartAt 𝒥 x).symm z)
    (mdifferentiableAt_extChartAt (I := 𝒥) hsrc)
  apply hh.congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_source.mem_nhds hsrc] with w hw
  have hw' : w ∈ (extChartAt 𝒥 x).source := by simpa only [extChartAt_source] using hw
  simp only [Function.comp_apply,(extChartAt 𝒥 x).left_inv hw']

lemma exists_nhds_nondifferentiable_null {u : M → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (x : M) :
    ∃ U ∈ 𝓝 x, (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure M)
      {y | y ∈ U ∧ ¬ MDifferentiableAt 𝒥 𝓘(ℝ,ℝ) u y} = 0 := by
  obtain ⟨C,r,hrpos,hr,hC⟩ := exists_lipschitzOn_inverse_chart (E := E) x
  let U := (extChartAt 𝒥 x).source ∩
    (extChartAt 𝒥 x) ⁻¹' ball (extChartAt 𝒥 x x) r
  have hU : U ∈ 𝓝 x := by
    apply inter_mem
    · simpa only [extChartAt_source] using chart_source_mem_nhds E x
    · exact (continuousAt_extChartAt x).preimage_mem_nhds (ball_mem_nhds _ hrpos)
  refine ⟨U,hU,?_⟩
  apply measure_mono_null _ (hausdorff_nondifferentiable_chart_image_null hu x hr hC)
  intro y hy
  exact ⟨⟨(extChartAt 𝒥 x) y,hy.1.2,(extChartAt 𝒥 x).left_inv hy.1.1⟩,hy.2⟩

lemma lipschitz_ae_mdifferentiable [CompactSpace M] {u : M → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) :
    ∀ᵐ x ∂(Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ) : Measure M),
      MDifferentiableAt 𝒥 𝓘(ℝ,ℝ) u x := by
  classical
  choose U hUnhds hUnull using exists_nhds_nondifferentiable_null (E := E) hu
  obtain ⟨s,_,hs⟩ := isCompact_univ.elim_nhds_subcover U (fun x _ => hUnhds x)
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ x ∈ (s : Set M),
    {y | y ∈ U x ∧ ¬ MDifferentiableAt 𝒥 𝓘(ℝ,ℝ) u y})
  · intro y hy
    obtain ⟨x,hx,hyx⟩ := mem_iUnion₂.mp (hs (mem_univ y))
    exact mem_iUnion₂.mpr ⟨x,hx,hyx,hy⟩
  · exact (measure_biUnion_null_iff s.countable_toSet).mpr (fun x _ => hUnull x)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ActiveDifferentiability
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ENNReal NNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma activeLog_derivative_eq {v : M → ℝ} (hv : Continuous v) {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ activeLogs v x)
    {D : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun h => cTransform v (riemannianExp x h)) D 0) :
    D = innerSL ℝ p := by
  have hID := contracted_minimizer_mem_injectivityDomain hp.1
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let f := fun h : TangentSpace 𝓘(ℝ,Model n) x =>
    cTransform v (riemannianExp x h) + 2 * normalCost x ((1/2:ℝ) • p) h
  have hmin : IsLocalMin f 0 := by
    apply Filter.Eventually.of_forall
    intro h
    have hh := active_split_lower_support hv hp.1 hp.2
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (riemannianExp x h)
    dsimp [f,normalCost]
    rw [riemannianExp_zero]
    linarith
  have hf : HasFDerivAt f (D - innerSL ℝ p) 0 := by
    apply (hD.add ((normalCost_hasFDerivAt_zero hID).const_mul 2)).congr_fderiv
    ext h
    simp only [_root_.add_apply,_root_.sub_apply,
      _root_.smul_apply,innerSL_apply_apply,inner_neg_left,
      real_inner_smul_left,smul_eq_mul]
    ring
  exact sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero hf)

lemma activeLogs_subsingleton_of_mdifferentiable {v : M → ℝ} (hv : Continuous v)
    {x : M} (hD : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) :
    (activeLogs (n := n) v x).Subsingleton := by
  have hD' : DifferentiableAt ℝ (fun h : TangentSpace 𝓘(ℝ,Model n) x => cTransform v (riemannianExp x h)) 0 := by
    have he := ((contMDiff_riemannianExp_fiber (n := n) x 0).mdifferentiableAt (by simp))
    have hD0 : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v)
        (riemannianExp (n := n) x 0) := by simpa only [riemannianExp_zero] using hD
    exact (hD0.comp 0 he).differentiableAt
  intro p hp q hq
  have hh := (activeLog_derivative_eq hv hp hD'.hasFDerivAt).symm.trans
    (activeLog_derivative_eq hv hq hD'.hasFDerivAt)
  apply ext_inner_right ℝ
  intro h
  exact congrArg (fun D : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => D h) hh

lemma contact_singleton_of_mdifferentiable {v : M → ℝ} (hv : Continuous v)
    {x : M} (hD : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {y z : M} (hy : contactGap (cTransform v) v x y = 0)
    (hz : contactGap (cTransform v) v x z = 0) : y = z := by
  obtain ⟨p,hp,hep⟩ := exists_minimizing_vector (n := n) x y
  obtain ⟨q,hq,heq⟩ := exists_minimizing_vector (n := n) x z
  have hp' : p ∈ activeLogs v x := ⟨hp,by simpa only [hep] using hy⟩
  have hq' : q ∈ activeLogs v x := ⟨hq,by simpa only [heq] using hz⟩
  have he := activeLogs_subsingleton_of_mdifferentiable hv hD hp' hq'
  exact hep.symm.trans ((congrArg (riemannianExp x) he).trans heq)

variable [MeasurableSpace M] [BorelSpace M]

lemma lipschitz_ae_mdifferentiable_metricVolume {u : M → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) :
    ∀ᵐ x ∂(metricVolume (M := M) n), MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) u x := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) := continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  have hh := lipschitz_ae_mdifferentiable (E := Model n) hu
  have hh' : ∀ᵐ x ∂(Measure.hausdorffMeasure (n : ℝ) : Measure M),
      MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) u x := by
    simpa [Model] using hh
  exact Measure.smul_absolutelyContinuous.ae_le hh'

lemma cTransform_ae_singleton_contacts [Nonempty M] {v : M → ℝ} (hv : Continuous v) :
    ∀ᵐ x ∂(metricVolume (M := M) n),
      ∀ y z : M, contactGap (cTransform v) v x y = 0 →
        contactGap (cTransform v) v x z = 0 → y = z := by
  have hlip := cTransform_lipschitz hv (D := ⟨Metric.diam (univ : Set M),Metric.diam_nonneg⟩)
    (fun x y => Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y))
  filter_upwards [lipschitz_ae_mdifferentiable_metricVolume (n := n) hlip] with x hx
  exact fun y z hy hz => contact_singleton_of_mdifferentiable hv hx hy hz

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ContinuousClosedRelationSelector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace WeakMTWTransport

lemma continuousAt_closed_relation_selector
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
    {R : Set (X × Y)} (hR : IsClosed R) {T : X → Y}
    (hT : ∀ x, (x,T x) ∈ R) {x : X}
    (hx : ∀ y, (x,y) ∈ R → y = T x) : ContinuousAt T x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let B : Set (X × Y) := R ∩ {z | ε ≤ dist z.2 (T x)}
  have hB : IsClosed B :=
    hR.inter (isClosed_le continuous_const (continuous_snd.dist continuous_const))
  have hclosed : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  have hxB : x ∈ (Prod.fst '' B)ᶜ := by
    rintro ⟨⟨a,b⟩, hab, hax⟩
    change a = x at hax
    subst a
    have hb := hx b hab.1
    have hdist := hab.2
    change ε ≤ dist b (T x) at hdist
    rw [hb,dist_self] at hdist
    exact (not_le.mpr hε) hdist
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hxB)
  refine ⟨δ,hδ,?_⟩
  intro a ha
  apply lt_of_not_ge
  intro han
  exact hd ha ⟨(a,T a),⟨hT a,han⟩,rfl⟩

lemma aemeasurable_closed_relation_selector
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Measure X} {R : Set (X × Y)} (hR : IsClosed R) {T : X → Y}
    (hT : ∀ x, (x,T x) ∈ R)
    (hsingle : ∀ᵐ x ∂μ, ∀ y, (x,y) ∈ R → y = T x) : AEMeasurable T μ := by
  let S : Set X := {x | ∀ y, (x,y) ∈ R → y = T x}
  have hS : ∀ᵐ x ∂μ, x ∈ S := hsingle
  have hSnull : NullMeasurableSet S μ := by
    have he : (univ : Set X) =ᵐ[μ] S := by
      filter_upwards [hS] with x hx
      exact propext ⟨fun _ => hx, fun _ => mem_univ x⟩
    exact nullMeasurableSet_univ.congr he
  have hc : ContinuousOn T S := by
    intro x hx
    exact (continuousAt_closed_relation_selector hR hT hx).continuousWithinAt
  have hm := hc.aemeasurable₀ hSnull
  rwa [Measure.restrict_eq_self_of_ae_mem hS] at hm

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CompactAE
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
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

namespace WeakMTWTransport

section CompactAE
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

omit [Nonempty M] in

lemma contact_gap_control_at (u v : M →ᵇ ℝ) (x y : M)
    (hsingle : ∀ z, contactGap u v x z = 0 → z = y)
    (hgap : ∀ z, 0 ≤ contactGap u v x z) (f : M →ᵇ ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z, contactGap u v x z ≤ δ → f y - f z ≤ ε := by
  let G : M → ℝ := fun z => contactGap u v x z
  let B : Set M := {z | ε ≤ f y - f z}
  have hG : Continuous G := (continuous_const.add (continuous_cost_right x)).add v.continuous
  have hB : IsCompact B := (isClosed_le continuous_const
    (continuous_const.sub f.continuous)).isCompact
  by_cases hne : B.Nonempty
  · obtain ⟨z,hz,hmin⟩ := hB.exists_isMinOn hne hG.continuousOn
    have hpos : 0 < G z := by
      apply lt_of_le_of_ne (hgap z)
      intro he
      have heq := hsingle z he.symm
      change ε ≤ f y - f z at hz
      rw [heq,sub_self] at hz
      exact (not_le.mpr hε) hz
    refine ⟨G z / 2,half_pos hpos,?_⟩
    intro w hw
    by_contra hn
    have hm := hmin (le_of_lt (lt_of_not_ge hn))
    change G z ≤ contactGap u v x w at hm
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro z _
    by_contra hn
    exact hne ⟨z,le_of_lt (lt_of_not_ge hn)⟩

lemma transform_perturbation_upper_at (u v : M →ᵇ ℝ) (x y : M)
    (hsingle : ∀ z, contactGap u v x z = 0 → z = y)
    (hgap : ∀ z, 0 ≤ contactGap u v x z) (f : M →ᵇ ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ t : ℝ, 0 < t → t ≤ τ →
      cTransform (fun z => v z + t * f z) x ≤ u x - t * f y + t * ε := by
  obtain ⟨δ,hδ,hcontrol⟩ := contact_gap_control_at u v x y hsingle hgap f hε
  have hden : 0 < 2 * ‖f‖ + 1 := by positivity
  refine ⟨δ / (2 * ‖f‖ + 1),div_pos hδ hden,?_⟩
  intro t ht htτ
  have htd : t * (2 * ‖f‖ + 1) ≤ δ := (le_div_iff₀ hden).mp htτ
  have htbound : t * (2 * ‖f‖) ≤ δ := by nlinarith
  rw [cTransform_le_iff (v := fun z => v z + t * f z)
    (v.continuous.add (continuous_const.mul f.continuous))]
  intro z
  have hg := hgap z
  have hbound : t * (f y - f z) ≤ contactGap u v x z + t * ε := by
    by_cases hs : contactGap u v x z ≤ δ
    · have hh := mul_le_mul_of_nonneg_left (hcontrol z hs) ht.le
      nlinarith
    · have hf1 := BoundedContinuousFunction.norm_coe_le_norm f y
      have hf2 := BoundedContinuousFunction.norm_coe_le_norm f z
      rw [Real.norm_eq_abs,abs_le] at hf1 hf2
      have hw : f y - f z ≤ 2 * ‖f‖ := by linarith [hf1.2,hf2.1]
      have hh := mul_le_mul_of_nonneg_left hw ht.le
      have hte : 0 ≤ t * ε := mul_nonneg ht.le hε.le
      linarith
  dsimp [contactGap] at hbound
  nlinarith

lemma transformedDifferenceQuotient_apply (v f : M →ᵇ ℝ) (t : ℝ) (x : M) :
    transformedDifferenceQuotient v f t x =
      (cTransform (fun z => v z + t * f z) x - cTransform v x) / t := by
  simp only [transformedDifferenceQuotient,BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.sub_apply,boundedCTransform_apply,smul_eq_mul]
  rw [div_eq_mul_inv,mul_comm]
  rfl

lemma transformedDifferenceQuotient_norm_le (v f : M →ᵇ ℝ) {t : ℝ} (ht : 0 < t) (x : M) :
    ‖transformedDifferenceQuotient v f t x‖ ≤ ‖f‖ := by
  have hh := boundedCTransform_nonexpansive (M := M) |>.dist_le_mul (v + t • f) v
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,add_sub_cancel_left,norm_smul,
    Real.norm_eq_abs,abs_of_pos ht] at hh
  have hp := BoundedContinuousFunction.norm_coe_le_norm
    (boundedCTransform (v + t • f) - boundedCTransform v) x
  have hbound := hp.trans hh
  rw [transformedDifferenceQuotient,BoundedContinuousFunction.smul_apply,norm_smul,
    Real.norm_eq_abs,abs_inv,abs_of_pos ht]
  exact (inv_mul_le_iff₀ ht).mpr hbound

lemma transformedDifferenceQuotient_tendsto_at (v f : M →ᵇ ℝ) (x y : M)
    (hcontact : contactGap (cTransform v) v x y = 0)
    (hsingle : ∀ z, contactGap (cTransform v) v x z = 0 → z = y)
    {s : ℕ → ℝ} (hs : ∀ j, 0 < s j) (hlim : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun j => transformedDifferenceQuotient v f (s j) x) atTop (𝓝 (-f y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨τ,hτ,hup⟩ := transform_perturbation_upper_at (boundedCTransform v) v x y
    hsingle (cTransform_gap_nonneg v.continuous x) f (half_pos hε)
  have hevent : ∀ᶠ j in atTop, s j ≤ τ :=
    (hlim.eventually (eventually_lt_nhds hτ)).mono fun _ h => h.le
  filter_upwards [hevent] with j hj
  rw [transformedDifferenceQuotient_apply,Real.dist_eq,sub_neg_eq_add,abs_lt]
  have hu := hup (s j) (hs j) hj
  have hl := cTransform_gap_nonneg
    (v.continuous.add (continuous_const.mul f.continuous) :
      Continuous (fun z => v z + s j * f z)) x y
  change cTransform (fun z => v z + s j * f z) x ≤
    cTransform v x - s j * f y + s j * (ε/2) at hu
  dsimp only [contactGap] at hcontact
  change 0 ≤ cTransform (fun z => v z + s j * f z) x + cost x y + (v y + s j * f y) at hl
  have hlo : -f y ≤ (cTransform (fun z => v z + s j * f z) x - cTransform v x) / s j := by
    apply (le_div_iff₀ (hs j)).mpr
    nlinarith
  have hhi : (cTransform (fun z => v z + s j * f z) x - cTransform v x) / s j ≤ -f y + ε/2 := by
    apply (div_le_iff₀ (hs j)).mpr
    nlinarith
  constructor <;> linarith

variable [MeasurableSpace M] [BorelSpace M]

lemma dual_minimum_ae_integral_eq (μ ν : Measure M) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (v : M →ᵇ ℝ) (T : M → M)
    (hcontact : ∀ x, contactGap (cTransform v) v x (T x) = 0)
    (hsingle : ∀ᵐ x ∂μ, ∀ y, contactGap (cTransform v) v x y = 0 → y = T x)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective μ ν (boundedCTransform v,v) ≤ dualObjective μ ν (a,b))
    (f : M →ᵇ ℝ) : (∫ x, f (T x) ∂μ) = ∫ y, f y ∂ν := by
  have hle (f : M →ᵇ ℝ) : (∫ x, f (T x) ∂μ) ≤ ∫ y, f y ∂ν := by
    let s : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
    have hs (j : ℕ) : 0 < s j := by dsimp [s] <;> positivity
    have hslim : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun j => ∫ x, transformedDifferenceQuotient v f (s j) x ∂μ)
        atTop (𝓝 (∫ x, -f (T x) ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      · intro j
        exact (transformedDifferenceQuotient v f (s j)).continuous.aestronglyMeasurable
      · exact integrable_const _
      · intro j
        exact Eventually.of_forall (transformedDifferenceQuotient_norm_le v f (hs j))
      · filter_upwards [hsingle] with x hx
        exact transformedDifferenceQuotient_tendsto_at v f x (T x) (hcontact x) hx hs hslim
    have hineq (j : ℕ) : -(∫ y, f y ∂ν) ≤
        ∫ x, transformedDifferenceQuotient v f (s j) x ∂μ := by
      let a := boundedCTransform (v + s j • f)
      let b : M →ᵇ ℝ := v + s j • f
      have hi := hmin a b (cTransform_gap_nonneg b.continuous)
      have hb : (∫ y, b y ∂ν) = (∫ y, v y ∂ν) + s j * ∫ y, f y ∂ν := by
        change (∫ y, v y + s j * f y ∂ν) = _
        rw [integral_add (v.integrable ν) ((f.integrable ν).const_mul (s j)),
          integral_const_mul]
      have hq : (∫ x, transformedDifferenceQuotient v f (s j) x ∂μ) =
          ((∫ x, a x ∂μ) - (∫ x, boundedCTransform v x ∂μ)) / s j := by
        change (∫ x, (s j)⁻¹ * (a x - boundedCTransform v x) ∂μ) = _
        rw [integral_const_mul,integral_sub (a.integrable μ) ((boundedCTransform v).integrable μ)]
        rw [div_eq_mul_inv,mul_comm]
      rw [hq]
      apply (le_div_iff₀ (hs j)).mpr
      change (∫ x, boundedCTransform v x ∂μ) + (∫ y, v y ∂ν) ≤
        (∫ x, a x ∂μ) + (∫ y, b y ∂ν) at hi
      rw [hb] at hi
      nlinarith
    have hbound := ge_of_tendsto' hlim hineq
    rw [integral_neg] at hbound
    linarith
  apply le_antisymm (hle f)
  have hneg := hle (-f)
  simp only [BoundedContinuousFunction.neg_apply,integral_neg] at hneg
  linarith

omit [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma cost_contact_relation_isClosed (u v : M →ᵇ ℝ) :
    IsClosed {z : M × M | contactGap u v z.1 z.2 = 0} := by
  apply isClosed_eq _ continuous_const
  exact ((u.continuous.comp continuous_fst).add
    (((continuous_fst.dist continuous_snd).pow 2).div_const 2)).add
    (v.continuous.comp continuous_snd)

lemma dual_minimum_ae_pushforward (μ ν : Measure M) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (v : M →ᵇ ℝ) (T : M → M)
    (hcontact : ∀ x, contactGap (cTransform v) v x (T x) = 0)
    (hsingle : ∀ᵐ x ∂μ, ∀ y, contactGap (cTransform v) v x y = 0 → y = T x)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective μ ν (boundedCTransform v,v) ≤ dualObjective μ ν (a,b)) :
    AEMeasurable T μ ∧ Measure.map T μ = ν := by
  have hT : AEMeasurable T μ := aemeasurable_closed_relation_selector
    (cost_contact_relation_isClosed (boundedCTransform v) v) hcontact hsingle
  refine ⟨hT,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hT f.continuous.aestronglyMeasurable]
  exact dual_minimum_ae_integral_eq μ ν v T hcontact hsingle hmin f

end CompactAE
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_DensityBounds
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

section DensityBounds
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
omit [MetricSpace M] [BorelSpace M] [CompactSpace M] in

lemma densityMeasure_bounds {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hrho : AdmissibleDensity vol lam cap rho) :
    ENNReal.ofReal lam • vol ≤ densityMeasure vol rho ∧
      densityMeasure vol rho ≤ ENNReal.ofReal cap • vol := by
  constructor
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hrho.2.2.2] with x hx
    exact ENNReal.ofReal_le_ofReal hx.1
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hrho.2.2.2] with x hx
    exact ENNReal.ofReal_le_ofReal hx.2

omit [MetricSpace M] [BorelSpace M] [CompactSpace M] in
lemma volume_absolutelyContinuous_densityMeasure {vol : Measure M} {lam cap : ℝ}
    {rho : M → ℝ} (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    vol ≪ densityMeasure vol rho := by
  apply withDensity_absolutelyContinuous' hrho.1.ennreal_ofReal
  filter_upwards [hrho.2.2.2] with x hx
  exact (ENNReal.ofReal_pos.mpr (hlam.trans_le hx.1)).ne'
end DensityBounds

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_MeasureContacts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ENNReal NNReal ContDiff Topology BoundedContinuousFunction

namespace WeakMTWTransport

section MeasureContacts
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

omit [CompactSpace M] [Nonempty M] [BorelSpace M] in

lemma dual_minimum_swap {μ ν : Measure M} {u v : M →ᵇ ℝ}
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective μ ν (u,v) ≤ dualObjective μ ν (a,b)) :
    ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective ν μ (v,u) ≤ dualObjective ν μ (a,b) := by
  intro a b hab
  have hh := hmin b a (fun x y => by rw [contactGap_symm]; exact hab y x)
  simpa only [dualObjective,add_comm] using hh

omit [CompactSpace M] [Nonempty M] [BorelSpace M] in

lemma contactImage_ae_eq_preimage {μ : Measure M} {u v : M → ℝ} {S : M → M}
    (hcontact : ∀ y, contactGap u v (S y) y = 0)
    (hsingle : ∀ᵐ y ∂μ, ∀ x, contactGap u v x y = 0 → x = S y)
    (A : Set M) : contactImage u v A =ᵐ[μ] S ⁻¹' A := by
  filter_upwards [hsingle] with y hy
  apply propext
  change (∃ x ∈ A, contactGap u v x y = 0) ↔ S y ∈ A
  constructor
  · rintro ⟨x,hx,hxy⟩
    simpa only [hy x hxy] using hx
  · intro hx
    exact ⟨S y,hx,hcontact y⟩

omit [CompactSpace M] [Nonempty M] [BorelSpace M] in

lemma contactImage_measure {μ ν : Measure M} {u v : M → ℝ} {S : M → M}
    (hcontact : ∀ y, contactGap u v (S y) y = 0)
    (hsingle : ∀ᵐ y ∂ν, ∀ x, contactGap u v x y = 0 → x = S y)
    (hS : AEMeasurable S ν) (hpush : Measure.map S ν = μ)
    {A : Set M} (hA : MeasurableSet A) :
    NullMeasurableSet (contactImage u v A) ν ∧ ν (contactImage u v A) = μ A := by
  have he := contactImage_ae_eq_preimage hcontact hsingle A
  refine ⟨?_,?_⟩
  · exact (hS.nullMeasurableSet_preimage hA).congr he.symm
  · rw [measure_congr he,← Measure.map_apply_of_aemeasurable hS hA,hpush]

omit [CompactSpace M] [Nonempty M] [BorelSpace M] in

lemma contactImage_volume_comparison {vol : Measure M} {lam cap : ℝ}
    {rho0 rho1 u v : M → ℝ}
    (hrho0 : AdmissibleDensity vol lam cap rho0)
    (hrho1 : AdmissibleDensity vol lam cap rho1)
    {A : Set M} (hmass : densityMeasure vol rho1 (contactImage u v A) =
      densityMeasure vol rho0 A) :
    ENNReal.ofReal lam * vol A ≤ ENNReal.ofReal cap * vol (contactImage u v A) ∧
    ENNReal.ofReal lam * vol (contactImage u v A) ≤ ENNReal.ofReal cap * vol A := by
  have h0 := densityMeasure_bounds hrho0
  have h1 := densityMeasure_bounds hrho1
  constructor
  · calc
      _ ≤ densityMeasure vol rho0 A := h0.1 A
      _ = densityMeasure vol rho1 (contactImage u v A) := hmass.symm
      _ ≤ _ := h1.2 (contactImage u v A)
  · calc
      _ ≤ densityMeasure vol rho1 (contactImage u v A) := h1.1 (contactImage u v A)
      _ = densityMeasure vol rho0 A := hmass
      _ ≤ _ := h0.2 A

end MeasureContacts

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_RiemannianTransport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ENNReal NNReal ContDiff Topology BoundedContinuousFunction

namespace WeakMTWTransport
section RiemannianTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma dual_minimizer_rough_transport {lam cap : ℝ} {rho0 rho1 : M → ℝ}
    (hlam : 0 < lam)
    (hrho0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (hrho1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (hdual : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b)) :
    ∃ T S : M → M,
      (∀ x, contactGap u v x (T x) = 0) ∧
      (∀ y, contactGap u v (S y) y = 0) ∧
      (∀ᵐ x ∂(metricVolume n), ∀ y, contactGap u v x y = 0 → y = T x) ∧
      (∀ᵐ y ∂(metricVolume n), ∀ x, contactGap u v x y = 0 → x = S y) ∧
      AEMeasurable T (densityMeasure (metricVolume n) rho0) ∧
      AEMeasurable S (densityMeasure (metricVolume n) rho1) ∧
      Measure.map T (densityMeasure (metricVolume n) rho0) = densityMeasure (metricVolume n) rho1 ∧
      Measure.map S (densityMeasure (metricVolume n) rho1) = densityMeasure (metricVolume n) rho0 := by
  have : IsProbabilityMeasure (densityMeasure (metricVolume n) rho0) :=
    densityMeasure_probability hlam hrho0
  have : IsProbabilityMeasure (densityMeasure (metricVolume n) rho1) :=
    densityMeasure_probability hlam hrho1
  have hcontactT : ∀ x : M, ∃ y : M, contactGap u v x y = 0 := by
    intro x
    obtain ⟨y,hy,_⟩ := exists_cTransform_contact v.continuous x
    refine ⟨y,?_⟩
    simp only [contactGap,hdual.1,hy]
    ring
  have hcontactS : ∀ y : M, ∃ x : M, contactGap u v x y = 0 := by
    intro y
    obtain ⟨x,hx,_⟩ := exists_cTransform_contact u.continuous y
    refine ⟨x,?_⟩
    rw [contactGap_symm]
    simp only [contactGap,hdual.2,hx]
    ring
  choose T hT using hcontactT
  choose S hS using hcontactS
  have hsingleT : ∀ᵐ x ∂(metricVolume n),
      ∀ y, contactGap u v x y = 0 → y = T x := by
    filter_upwards [cTransform_ae_singleton_contacts (n := n) v.continuous] with x hx
    intro y hy
    exact hx y (T x) (by simpa only [← hdual.1] using hy)
      (by simpa only [← hdual.1] using hT x)
  have hsingleS : ∀ᵐ y ∂(metricVolume n),
      ∀ x, contactGap u v x y = 0 → x = S y := by
    filter_upwards [cTransform_ae_singleton_contacts (n := n) u.continuous] with y hy
    intro x hx
    apply hy x (S y)
    · simpa only [← hdual.2,← contactGap_symm u v x y] using hx
    · simpa only [← hdual.2,← contactGap_symm u v (S y) y] using hS y
  have hmaybeT := dual_minimum_ae_pushforward
    (densityMeasure (metricVolume n) rho0) (densityMeasure (metricVolume n) rho1) v T
    (by simpa only [← hdual.1] using hT)
    (by
      have he := (withDensity_absolutelyContinuous (metricVolume n)
        (fun x => ENNReal.ofReal (rho0 x))).ae_le hsingleT
      filter_upwards [he] with x hx
      intro y hy
      exact hx y (by simpa only [← hdual.1] using hy))
    (by
      have he : boundedCTransform v = u := by
        ext x; exact congrFun hdual.1.symm x
      simpa only [he] using hmin)
  have hmaybeS := dual_minimum_ae_pushforward
    (densityMeasure (metricVolume n) rho1) (densityMeasure (metricVolume n) rho0) u S
    (by intro y; simpa only [← hdual.2,← contactGap_symm u v (S y) y] using hS y)
    (by
      filter_upwards [(withDensity_absolutelyContinuous (metricVolume n) _).ae_le hsingleS] with y hy
      intro x hx
      apply hy x
      simpa only [← hdual.2,← contactGap_symm u v x y] using hx)
    (by
      have he : boundedCTransform u = v := by
        ext x; exact congrFun hdual.2.symm x
      simpa only [he] using dual_minimum_swap hmin)
  exact ⟨T,S,hT,hS,hsingleT,hsingleS,hmaybeT.1,hmaybeS.1,hmaybeT.2,hmaybeS.2⟩

lemma dual_minimizer_contactImage_mass {lam cap : ℝ} {rho0 rho1 : M → ℝ}
    (hlam : 0 < lam)
    (hrho0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (hrho1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (hdual : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b))
    {A : Set M} (hA : MeasurableSet A) :
    NullMeasurableSet (contactImage u v A) (metricVolume n) ∧
      densityMeasure (metricVolume n) rho1 (contactImage u v A) =
        densityMeasure (metricVolume n) rho0 A ∧
      ENNReal.ofReal lam * metricVolume n A ≤
        ENNReal.ofReal cap * metricVolume n (contactImage u v A) ∧
      ENNReal.ofReal lam * metricVolume n (contactImage u v A) ≤
        ENNReal.ofReal cap * metricVolume n A := by
  obtain ⟨T,S,_,hS,_,hsingleS,_,hSmeas,_,hpushS⟩ :=
    dual_minimizer_rough_transport hlam hrho0 hrho1 hdual hmin
  have hs : ∀ᵐ y ∂(densityMeasure (metricVolume n) rho1),
      ∀ x, contactGap u v x y = 0 → x = S y :=
    (withDensity_absolutelyContinuous (metricVolume n) _).ae_le hsingleS
  have hm := contactImage_measure hS hs hSmeas hpushS hA
  refine ⟨?_,hm.2,(contactImage_volume_comparison hrho0 hrho1 hm.2).1,
    (contactImage_volume_comparison hrho0 hrho1 hm.2).2⟩
  exact hm.1.mono_ac (volume_absolutelyContinuous_densityMeasure hlam hrho1)

end RiemannianTransport
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_EuclideanVolumeFactorNe
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner _root_.OAI.WeakMTWTransport.riemannianExp_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Metric Bundle
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport

lemma euclideanVolumeFactor_ne_zero (n : ℕ) : euclideanVolumeFactor n≠0 := by
  have hdim : (Module.finrank ℝ (Model n):ℝ)=(n:ℝ) := by simp [Model]
  have hH : (Measure.hausdorffMeasure (n:ℝ) : Measure (Model n)).IsAddHaarMeasure := by
    rw [←hdim]; infer_instance
  exact ENNReal.div_ne_zero.mpr ⟨(measure_ball_pos volume (0:Model n) zero_lt_one).ne',
    measure_ball_lt_top.ne⟩

lemma euclideanVolumeFactor_ne_top (n : ℕ) : euclideanVolumeFactor n≠⊤ := by
  have hdim : (Module.finrank ℝ (Model n):ℝ)=(n:ℝ) := by simp [Model]
  have hH : (Measure.hausdorffMeasure (n:ℝ) : Measure (Model n)).IsAddHaarMeasure := by
    rw [←hdim]; infer_instance
  exact ENNReal.div_ne_top measure_ball_lt_top.ne
    (measure_ball_pos _ (0:Model n) zero_lt_one).ne'

instance metricVolume_model_haar (n : ℕ) :
    (metricVolume (M := Model n) n).IsAddHaarMeasure := by
  have hdim : (Module.finrank ℝ (Model n):ℝ)=(n:ℝ) := by simp [Model]
  have hH : (Measure.hausdorffMeasure (n:ℝ) : Measure (Model n)).IsAddHaarMeasure := by
    rw [←hdim]; infer_instance
  exact Measure.IsAddHaarMeasure.smul _ (euclideanVolumeFactor_ne_zero n)
    (euclideanVolumeFactor_ne_top n)

lemma lipschitzOn_metricVolume_image_le {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {C : ℝ≥0} {f : X → Y} {s : Set X} (hf : LipschitzOnWith C f s) (n : ℕ) :
    metricVolume n (f '' s)≤(C:ℝ≥0∞)^n*metricVolume n s := by
  have H := hf.hausdorffMeasure_image_le (d := (n:ℝ)) (by positivity)
  have hh := mul_le_mul_right H (euclideanVolumeFactor n)
  simpa only [metricVolume,Measure.smul_apply,smul_eq_mul,ENNReal.rpow_natCast,
    mul_assoc,mul_comm,mul_left_comm] using hh

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactRelationChart
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section ContactRelationChart
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma chartContactRelation_volume_upper {lam cap : ℝ} {rho0 rho1 : M → ℝ}
    (hlam : 0 < lam)
    (hrho0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (hrho1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (hdual : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b))
    {a b : M} {A : Set (Model n)} {T : Set M} (hA : MeasurableSet A)
    (ha : A⊆(extChartAt 𝓘(ℝ,Model n) a).target) {Da Cb : ℝ≥0}
    (hDa : LipschitzOnWith Da (extChartAt 𝓘(ℝ,Model n) a).symm A)
    (hCb : LipschitzOnWith Cb (extChartAt 𝓘(ℝ,Model n) b) T) :
    ENNReal.ofReal lam*metricVolume n {q | ∃ z∈A, chartContactRelation a b u v T z q} ≤
      ENNReal.ofReal cap*((Cb:ℝ≥0∞)*(Da:ℝ≥0∞))^n*metricVolume n A := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let ψ := extChartAt 𝓘(ℝ,Model n) b
  let X := χ.symm '' A
  let Y := contactImage u v X
  have hXm : MeasurableSet X := hA.image_of_continuousOn_injOn
    ((continuousOn_extChartAt_symm a).mono ha) (χ.symm.injOn.mono ha)
  have hmass := (dual_minimizer_contactImage_mass hlam hrho0 hrho1 hdual hmin hXm).2.2.2
  have hsub : {q | ∃ z∈A, chartContactRelation a b u v T z q}⊆ψ '' (Y∩T) := by
    rintro q ⟨z,hz,hq,hqT,hgap⟩
    refine ⟨ψ.symm q,⟨?_,hqT⟩,ψ.right_inv hq⟩
    exact ⟨χ.symm z,⟨z,hz,rfl⟩,hgap⟩
  have h1 := lipschitzOn_metricVolume_image_le (hCb.mono inter_subset_right :
    LipschitzOnWith Cb ψ (Y∩T)) n
  have h2 := lipschitzOn_metricVolume_image_le hDa n
  calc
    _ ≤ ENNReal.ofReal lam*metricVolume n (ψ '' (Y∩T)) :=
      mul_le_mul_right (measure_mono hsub) _
    _ ≤ ENNReal.ofReal lam*((Cb:ℝ≥0∞)^n*metricVolume n (Y∩T)) :=
      mul_le_mul_right h1 _
    _ ≤ ENNReal.ofReal lam*((Cb:ℝ≥0∞)^n*metricVolume n Y) :=
      mul_le_mul_right (mul_le_mul_right (measure_mono inter_subset_left) _) _
    _ = (Cb:ℝ≥0∞)^n*(ENNReal.ofReal lam*metricVolume n Y) := by ac_rfl
    _ ≤ (Cb:ℝ≥0∞)^n*(ENNReal.ofReal cap*metricVolume n X) :=
      mul_le_mul_right hmass _
    _ ≤ (Cb:ℝ≥0∞)^n*(ENNReal.ofReal cap*((Da:ℝ≥0∞)^n*metricVolume n A)) :=
      mul_le_mul_right (mul_le_mul_right h2 _) _
    _ = _ := by rw [mul_pow]; ac_rfl

end ContactRelationChart
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section AllLocalContact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.local_contact_global (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {x y : M}
    (hmin : IsLocalMin (fun z => u z+cost z y) x) : contactGap u v x y=0 := by
  obtain ⟨p,hp,rfl⟩ := exists_minimizing_vector (n := n) x y
  have ht : (0:ℝ)<1/2 := by norm_num
  have ht1 : (1:ℝ)/2<1 := by norm_num
  have hID := contracted_minimizer_mem_injectivityDomain hp ht ht1
  have hcon := splitNormalAction_contact hp ht ht1
  simp only [splitNormalAction,normalCost,riemannianExp_zero] at hcon
  have hsub : p∈normalSubdifferential u x := by
    apply local_min_divided_cost_subgradient (t := 1/2) (by norm_num) hID
    filter_upwards [hmin] with z hz
    have H := squared_dist_divided_action_le z
      (riemannianExp x ((1/2:ℝ) • p)) (riemannianExp x p) ht ht1
    have H' : cost z (riemannianExp x p)≤
        cost z (riemannianExp x ((1/2:ℝ) • p))/(1/2)+
          cost (riemannianExp x ((1/2:ℝ) • p)) (riemannianExp x p)/(1-1/2) := by
      convert H using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [cost,div_div])
    linarith only [hz,H',hcon]
  rw [hdual.1] at hsub
  have H := (hmtw.global_support hv hsub).2
  rw [←hdual.1] at H
  have hupp : v (riemannianExp x p)≤-cost (riemannianExp x p) x-u x := by
    rw [hdual.2,cTransform_le_iff hu]
    intro a
    have h := H a
    rw [cost_symm a,cost_symm x] at h
    linarith only [h]
  have hgap := dualPair_gap_nonneg hv hdual x (riemannianExp x p)
  dsimp only [contactGap] at hgap ⊢
  rw [cost_symm (riemannianExp x p)] at hupp
  linarith only [hgap,hupp]

lemma WeakMTW.chart_local_contact_global (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a : M} {z : Model n} {y : M}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hmin : IsLocalMin (fun w => u ((extChartAt 𝓘(ℝ,Model n) a).symm w)+
      cost ((extChartAt 𝓘(ℝ,Model n) a).symm w) y) z) :
    contactGap u v ((extChartAt 𝓘(ℝ,Model n) a).symm z) y=0 := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  have hx : χ.symm z∈χ.source := χ.map_target hz
  have hc : ContinuousAt χ (χ.symm z) :=
    (continuousOn_extChartAt a (χ.symm z) hx).continuousAt
      ((isOpen_extChartAt_source a).mem_nhds hx)
  have hm : ∀ᶠ x in 𝓝 (χ.symm z), u (χ.symm z)+cost (χ.symm z) y≤u x+cost x y := by
    have H : ∀ᶠ x in 𝓝 (χ.symm z),
        u (χ.symm z)+cost (χ.symm z) y≤u (χ.symm (χ x))+cost (χ.symm (χ x)) y := by
      have HH := hc.eventually (χ.right_inv hz ▸ hmin)
      simpa only [show extChartAt 𝓘(ℝ,Model n) a=χ from rfl,χ.right_inv hz] using HH
    filter_upwards [H,(isOpen_extChartAt_source a).mem_nhds hx] with x hx1 hx2
    simpa only [χ.left_inv hx2] using hx1
  exact hmtw.local_contact_global hu hv hdual hm

end AllLocalContact
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartGradientMap
attribute [-instance] _root_.OAI.WeakMTWTransport.metricVolume_model_haar
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

omit [CompactSpace M] [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinateRaise_contDiffAt {a : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (fun q : Model n×(Model n →L[ℝ] ℝ) =>
      (q.1,(riemannianCoordinateMetric a q.1).inverse q.2)) q := by
  have hg := (contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hq)
  have hi := (riemannianCoordinateMetric_isInvertible hq).contDiffAt_map_inverse.comp q.1 hg
  exact contDiffAt_fst.prodMk ((hi.comp q contDiffAt_fst).clm_apply contDiffAt_snd)

omit [CompactSpace M] [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartGradientVector_total_continuousAt {a : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContinuousAt (fun q : Model n×(Model n →L[ℝ] ℝ) =>
      (⟨(extChartAt 𝓘(ℝ,Model n) a).symm q.1,chartGradientVector a q.1 q.2⟩ :
        TangentBundle 𝓘(ℝ,Model n) M)) q := by
  let c := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  let f := fun q : Model n×(Model n →L[ℝ] ℝ) =>
    (q.1,(riemannianCoordinateMetric a q.1).inverse q.2)
  have hT : f q∈c.target := (tangent_chart_target_iff _ (f q)).mpr hq
  have hc : ContinuousAt c.symm (f q) :=
    (continuousOn_extChartAt_symm _).continuousAt ((isOpen_extChartAt_target _).mem_nhds hT)
  have hf : ContinuousAt f q := (coordinateRaise_contDiffAt hq).continuousAt
  apply (hc.comp (x := q) hf).congr_of_eventuallyEq
  have he : ∀ᶠ q' : Model n×(Model n →L[ℝ] ℝ) in 𝓝 q,
      q'.1∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target a).mem_nhds hq)
  filter_upwards [he] with q' hq'
  exact chartGradientVector_total_eq hq'

omit [Nonempty M] in
lemma chartGradientVector_regular_near {a : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : chartGradientVector a q.1 q.2∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1)) :
    ∀ᶠ q' : Model n×(Model n →L[ℝ] ℝ) in 𝓝 q,
      chartGradientVector a q'.1 q'.2∈injectivityDomain
        ((extChartAt 𝓘(ℝ,Model n) a).symm q'.1) :=
  (chartGradientVector_total_continuousAt hq).preimage_mem_nhds
    (isOpen_total_injectivityDomain.mem_nhds hp)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_LocalMountains
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
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace Y]

lemma lower_support_of_nonnegative_hessian {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S) (hf : ∀ z∈S, ContDiffAt ℝ 2 f z)
    (hH : ∀ z∈S, ∀ d : E, 0 ≤ fderiv ℝ (fderiv ℝ f) z d d)
    {x y : E} (hx : x∈S) (hy : y∈S) :
    f x+fderiv ℝ f x (y-x) ≤ f y := by
  let d := y-x
  let l : ℝ → E := fun t => x+t • d
  let g : ℝ → ℝ := fun t => f (l t)
  let g' : ℝ → ℝ := fun t => fderiv ℝ f (l t) d
  let g'' : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ f) (l t) d d
  have hl : ∀ t∈Icc (0:ℝ) 1, l t∈S := by
    intro t ht
    have H := hS hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [l,d]
    module
  have hld (t : ℝ) : HasDerivAt l d t := by
    simpa only [l,id_eq,one_smul] using (((hasDerivAt_id t).smul_const d).const_add x)
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g (g' t) t :=
    ((hf (l t) (hl t ht)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hld t)
  have hg' (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g' (g'' t) t := by
    have H := (((hf (l t) (hl t ht)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hld t)
    simpa only [g',g'',Function.comp_apply,map_zero,add_zero] using H.clm_apply (hasDerivAt_const t d)
  have hconv : ConvexOn ℝ (Icc (0:ℝ) 1) g :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => (hg' t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hH _ (hl t (interior_subset ht)) d)
  have H := hconv.deriv_le_slope (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one) zero_lt_one (hg 0 (by constructor <;> norm_num)).differentiableAt
  rw [(hg 0 (by constructor <;> norm_num)).deriv] at H
  simp only [g,g',l,d,zero_smul,add_zero,one_smul,add_sub_cancel,slope,
    sub_zero,inv_one,one_smul,vsub_eq_sub] at H
  linarith

lemma bilinear_nonnegative_of_norm_sub_le {B H : E →L[ℝ] E →L[ℝ] ℝ} {m : ℝ}
    (hB : ∀ d, m*‖d‖^2 ≤ B d d) (hH : ‖H-B‖≤ m) (d : E) : 0≤H d d := by
  have hn := (H-B).le_opNorm₂ d d
  have hmul := mul_le_mul_of_nonneg_right hH (sq_nonneg ‖d‖)
  have hdiff : H d d-B d d ≤ ‖(H-B) d d‖ := le_abs_self _
  have hdiff' : -(H d d-B d d) ≤ ‖(H-B) d d‖ := neg_le_abs _
  have he : ‖H-B‖*‖d‖*‖d‖=‖H-B‖*‖d‖^2 := by ring
  rw [he] at hn
  have H' := hB d
  nlinarith

lemma exists_local_mountains {F : Y → E → ℝ} {x : E} {y : Y} {m : ℝ}
    (hm : 0< m)
    (hC : ContinuousAt (fun q : E×Y => fderiv ℝ (fderiv ℝ (F q.2)) q.1) (x,y))
    (hD : ∀ᶠ q : E×Y in 𝓝 (x,y), ContDiffAt ℝ 2 (F q.2) q.1)
    (hpos : ∀ d:E, m*‖d‖^2 ≤ fderiv ℝ (fderiv ℝ (F y)) x d d) :
    ∃ r>0, ∃ V∈𝓝 y, ∀ y'∈V, ∀ z∈Metric.closedBall x r,
      fderiv ℝ (F y') z=0 → ∀ w∈Metric.closedBall x r, F y' z≤F y' w := by
  have H := @ContinuousAt.norm (E×Y) (E →L[ℝ] E →L[ℝ] ℝ) _ _ _ _
    (hC.sub (continuousAt_const (y := fderiv ℝ (fderiv ℝ (F y)) x)))
  have Hn : ∀ᶠ q : E×Y in 𝓝 (x,y),
      ‖fderiv ℝ (fderiv ℝ (F q.2)) q.1-fderiv ℝ (fderiv ℝ (F y)) x‖< m := by
    apply H.eventually_lt continuousAt_const
    simpa only [Pi.sub_apply,Prod.fst,Prod.snd,sub_self,ContinuousLinearMap.opNorm_zero] using hm
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp (Hn.and hD)
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  refine ⟨r,hr,V,hV,?_⟩
  intro y' hy' z hz hs w hw
  have Hlow := lower_support_of_nonnegative_hessian (f := F y') (convex_closedBall x r)
    (fun u hu => (hUV (a := (u,y')) ⟨hrU hu,hy'⟩).2)
    (fun u hu d => bilinear_nonnegative_of_norm_sub_le hpos
      (hUV (a := (u,y')) ⟨hrU hu,hy'⟩).1.le d) hz hw
  simpa only [hs,zero_apply,add_zero] using Hlow

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_TestMountains
attribute [-instance] _root_.OAI.WeakMTWTransport.metricVolume_model_haar
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
section TestMountains
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma exists_test_mountains {a : M} {z : Model n} {φ : Model n → ℝ} {m : ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hp : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z)) (hm : 0 < m)
    (hpos : ∀ d : Model n, m*‖d‖^2 ≤
      fderiv ℝ (fderiv ℝ φ) z d d +
      fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d) :
    ∃ r>0, Metric.closedBall z r⊆(extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ w∈Metric.closedBall z r, ∀ q∈Metric.closedBall z r,
        φ w+chartCost a (coordinateBackward a (-1,w,fderiv ℝ φ w)) w ≤
          φ q+chartCost a (coordinateBackward a (-1,w,fderiv ℝ φ w)) q := by
  let Y := fun w => coordinateBackward a (-1,w,fderiv ℝ φ w)
  let F := fun y w => φ w+chartCost a y w
  have hc : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) ((extChartAt 𝓘(ℝ,Model n) a).symm z,Y z) := by
    rw [show Y z=riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm z)
      (chartGradientVector a z (fderiv ℝ φ z)) from coordinateBackward_eq_exp_chartGradient hz _]
    exact cost_contMDiffAt_of_injectivityDomain
      (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,chartGradientVector a z (fderiv ℝ φ z)⟩ :
        TangentBundle 𝓘(ℝ,Model n) M) hp
  obtain ⟨hC,hD⟩ := chartCost_jet_continuous hz hc
  have hDn : ∀ᶠ q : Model n×M in 𝓝 (z,Y z), ContDiffAt ℝ 2 φ q.1 :=
    continuousAt_fst.eventually (hφ.eventually (by norm_num))
  have he : ∀ᶠ q : Model n×M in 𝓝 (z,Y z),
      fderiv ℝ (fderiv ℝ (F q.2)) q.1 =
        fderiv ℝ (fderiv ℝ φ) q.1+fderiv ℝ (fderiv ℝ (chartCost a q.2)) q.1 := by
    filter_upwards [hDn,hD] with q hq hq'
    exact second_fderiv_add_eq hq hq'
  have hFC : ContinuousAt (fun q : Model n×M => fderiv ℝ (fderiv ℝ (F q.2)) q.1) (z,Y z) := by
    apply ((((hφ.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt.comp continuousAt_fst).add hC).congr_of_eventuallyEq he
  have hFD : ∀ᶠ q : Model n×M in 𝓝 (z,Y z), ContDiffAt ℝ 2 (F q.2) q.1 := by
    filter_upwards [hDn,hD] with q hq hq'
    exact hq.add hq'
  obtain ⟨r₀,hr₀,V,hV,H⟩ := exists_local_mountains hm hFC hFD (by
    intro d
    rw [he.self_of_nhds]
    exact hpos d)
  have hj : ContinuousAt (fun w : Model n => (w,fderiv ℝ φ w)) z :=
    continuousAt_id.prodMk ((hφ.fderiv_right (m := 1) (by norm_num)).continuousAt)
  have hY : ContinuousAt Y z :=
    (coordinateBackward_contMDiffAt (q := (-1,z,fderiv ℝ φ z)) hz).continuousAt.comp (x := z) (f := fun w : Model n => ((-1:ℝ),w,fderiv ℝ φ w))
      (continuousAt_const.prodMk hj)
  have hchart : ∀ᶠ w : Model n in 𝓝 z, w∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (isOpen_extChartAt_target a).mem_nhds hz
  have hnear : ∀ᶠ w : Model n in 𝓝 z,
      w∈(extChartAt 𝓘(ℝ,Model n) a).target ∧
      chartGradientVector a w (fderiv ℝ φ w)∈injectivityDomain
        ((extChartAt 𝓘(ℝ,Model n) a).symm w) ∧
      ContDiffAt ℝ 2 φ w ∧ Y w∈V ∧ w∈Metric.ball z r₀ :=
    by
      filter_upwards [hchart,hj.eventually (chartGradientVector_regular_near hz hp),
        hφ.eventually (by norm_num),hY.preimage_mem_nhds hV,Metric.ball_mem_nhds z hr₀]
        with w hw hpw hφw hyw hrw
      exact ⟨hw,hpw,hφw,hyw,hrw⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  refine ⟨r,hr,fun w hw => (hrsub hw).1,?_⟩
  intro w hw q hq
  have hw' := hrsub hw
  apply H (Y w) hw'.2.2.2.1 w (Metric.ball_subset_closedBall hw'.2.2.2.2) ?_
    q (Metric.ball_subset_closedBall (hrsub hq).2.2.2.2)
  have HD := (hw'.2.2.1.differentiableAt (by norm_num)).hasFDerivAt.add
    (chartCost_gradient_at_contact hw'.1 hw'.2.1)
  change fderiv ℝ (φ + chartCost a (coordinateBackward a (-1,w,fderiv ℝ φ w))) w=0
  simpa only [add_neg_cancel] using HD.fderiv

end TestMountains
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_LocalJacobianBarrier
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace WeakMTWTransport
section LocalJacobianBarrier
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma abs_det_le_of_small_image_bounds {f : E → E} {A : E →L[ℝ] E} {x : E}
    (hf : HasStrictFDerivAt f A x) {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ U∈𝓝 x, ∃ s : Set E, s⊆U ∧ μ s≠0 ∧ μ s≠⊤ ∧
      μ (f '' s) ≤ ENNReal.ofReal C*μ s) : |A.det| ≤ C := by
  by_contra hbound
  have hbound : C < |A.det| := lt_of_not_ge hbound
  let m : ℝ≥0 := ⟨(C+|A.det|)/2,by positivity⟩
  have hmlo : C < (m:ℝ) := by change C < (C+|A.det|)/2; linarith only [hbound]
  have hmhi : (m:ℝ) < |A.det| := by change (C+|A.det|)/2 < |A.det|; linarith only [hbound]
  have hm : (m:ℝ≥0∞) < ENNReal.ofReal |A.det| := by
    rw [←ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_lt_ofReal_iff (hC.trans_lt hbound) |>.mpr hmhi
  have hpos : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ,hδ,Hδ⟩ := (hpos.and (mul_le_addHaar_image_of_lt_det μ A hm)).exists
  obtain ⟨U,hU,happrox⟩ := hf.approximates_deriv_on_nhds (Or.inr hδ)
  obtain ⟨s,hs,hs0,hsfin,hsimage⟩ := hsmall U hU
  have H := (Hδ s f (happrox.mono_set hs)).trans hsimage
  have Hm : (m:ℝ≥0∞) ≤ ENNReal.ofReal C :=
    (ENNReal.mul_le_mul_iff_left hs0 hsfin).mp H
  rw [←ENNReal.ofReal_coe_nnreal] at Hm
  have Hm' : (m:ℝ) ≤ C := (ENNReal.ofReal_le_ofReal_iff hC).mp Hm
  exact (not_le_of_gt hmlo) Hm'

end LocalJacobianBarrier
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_LowerTestContact
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
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace WeakMTWTransport
section LowerTestContact
variable {X Y : Type*} [MetricSpace X] [ProperSpace X]

lemma lower_test_sublevel_contacts {v φ : X → ℝ} {c : X → Y → ℝ}
    {S : X → Y} {R : X → Y → Prop} {x : X} {r h : ℝ} (hr : 0 < r)
    (hv : ContinuousOn v (Metric.closedBall x r))
    (hc : ∀ y, ContinuousOn (fun w => c w y) (Metric.closedBall x r))
    (hboundary : ∀ w, dist w x=r → h ≤ v w-φ w)
    (hlocal : ∀ w∈Metric.ball x r, ∀ z∈Metric.ball x r,
      IsLocalMin (fun w => v w+c w (S z)) w → R w (S z))
    (hmountain : ∀ z∈Metric.ball x r, v z-φ z < h →
      ∀ w∈Metric.closedBall x r, φ z+c z (S z) ≤ φ w+c w (S z)) :
    ∀ z∈Metric.ball x r, v z-φ z < h →
      ∃ w∈Metric.ball x r, v w-φ w < h ∧ R w (S z) := by
  intro z hz hzgap
  have hzclosed : z∈Metric.closedBall x r := Metric.ball_subset_closedBall hz
  obtain ⟨w,hw,hmin⟩ := (isCompact_closedBall x r).exists_isMinOn
    (Metric.nonempty_closedBall.mpr hr.le) (hv.add (hc (S z)))
  have hvalue : v w+c w (S z) ≤ v z+c z (S z) := hmin hzclosed
  have hmount : φ z+c z (S z) ≤ φ w+c w (S z) := hmountain z hz hzgap w hw
  have hwgap : v w-φ w < h := by linarith only [hvalue,hmount,hzgap]
  have hwin : w∈Metric.ball x r := by
    apply lt_of_le_of_ne (Metric.mem_closedBall.mp hw)
    intro he
    exact (not_le_of_gt hwgap) (hboundary w he)
  refine ⟨w,hwin,hwgap,hlocal w hwin z hz ?_⟩
  exact hmin.isLocalMin (Metric.closedBall_mem_nhds_of_mem hwin)

end LowerTestContact
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace WeakMTWTransport
section LowerTestViscosity
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma lower_test_abs_det_le {v φ : E → ℝ} {c : E → E → ℝ}
    {S : E → E} {R : E → E → Prop} {x : E} {r₀ ε C : ℝ}
    {A : E →L[ℝ] E} (hr₀ : 0 < r₀) (hε : 0 < ε) (hC : 0 ≤ C)
    (hv : ContinuousOn v (Metric.closedBall x r₀))
    (hφ : ContinuousOn φ (Metric.closedBall x r₀))
    (hc : ∀ y, ContinuousOn (fun w => c w y) (Metric.closedBall x r₀))
    (hx : v x=φ x)
    (hgap : ∀ w∈Metric.closedBall x r₀, ε*dist w x^2 ≤ v w-φ w)
    (hlocal : ∀ w∈Metric.ball x r₀, ∀ z∈Metric.ball x r₀,
      IsLocalMin (fun w => v w+c w (S z)) w → R w (S z))
    (hmountain : ∀ z∈Metric.ball x r₀, ∀ w∈Metric.closedBall x r₀,
      φ z+c z (S z) ≤ φ w+c w (S z))
    (hvol : ∀ s : Set E, MeasurableSet s → s⊆Metric.ball x r₀ →
      μ {y | ∃ w∈s, R w y} ≤ ENNReal.ofReal C*μ s)
    (hS : HasStrictFDerivAt S A x) : |A.det| ≤ C := by
  apply abs_det_le_of_small_image_bounds μ hS hC
  intro U hU
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem hU (Metric.ball_mem_nhds x hr₀))
  have hrsub : Metric.closedBall x r ⊆ Metric.closedBall x r₀ :=
    fun w hw => Metric.ball_subset_closedBall (hrU hw).2
  have hrb : Metric.ball x r ⊆ Metric.ball x r₀ :=
    fun w hw => (hrU (Metric.ball_subset_closedBall hw)).2
  let h := ε*r^2/2
  have hh : 0 < h := by dsimp [h] <;> positivity
  let Ω : Set E := Metric.ball x r ∩ {w | v w-φ w < h}
  have hΩopen : IsOpen Ω :=
    ((hv.sub hφ).mono (fun w hw => hrsub (Metric.ball_subset_closedBall hw))).isOpen_inter_preimage
      Metric.isOpen_ball isOpen_Iio
  have hxΩ : x∈Ω := by
    exact ⟨Metric.mem_ball_self hr,by change v x-φ x < h; simpa only [hx,sub_self] using hh⟩
  have hΩsub : Ω⊆Metric.ball x r₀ := fun w hw => hrb hw.1
  have hcontact : S '' Ω ⊆ {y | ∃ w∈Ω, R w y} := by
    rintro y ⟨z,hz,rfl⟩
    obtain ⟨w,hw,hwh,hwR⟩ := lower_test_sublevel_contacts hr
      (hv.mono hrsub) (fun y => (hc y).mono hrsub) (h := h)
      (fun w he => by
        have H := hgap w (hrsub (Metric.mem_closedBall.mpr he.le))
        rw [he] at H
        have H' : ε*r^2/2 ≤ ε*r^2 := by nlinarith only [mul_nonneg hε.le (sq_nonneg r)]
        exact H'.trans H)
      (fun w hw z hz => hlocal w (hrb hw) z (hrb hz))
      (fun z hz _ w hw => hmountain z (hrb hz) w (hrsub hw)) z hz.1 hz.2
    exact ⟨w,⟨hw,hwh⟩,hwR⟩
  refine ⟨Ω,fun w hw => (hrU (Metric.ball_subset_closedBall hw.1)).1,
    (hΩopen.measure_pos μ ⟨x,hxΩ⟩).ne',?_,?_⟩
  · exact ne_top_of_le_ne_top (isCompact_closedBall x r).measure_lt_top.ne
      (measure_mono (fun w hw => Metric.ball_subset_closedBall hw.1))
  · exact (measure_mono hcontact).trans (hvol Ω hΩopen.measurableSet hΩsub)

end LowerTestViscosity
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ActualLowerTestBound
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section ActualLowerTestBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.lower_test_chart_det_bound (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} {rho0 rho1 : M → ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hrho0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (hrho1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (hdual : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b))
    {a b : M} {z : Model n} {r ε : ℝ} {T : Set M} {Da Cb : ℝ≥0}
    {φ : Model n → ℝ} {S : Model n → Model n} {J : Model n →L[ℝ] Model n}
    (hr : 0 < r) (hε : 0 < ε)
    (hchart : Metric.closedBall z r⊆(extChartAt 𝓘(ℝ,Model n) a).target)
    (hDa : LipschitzOnWith Da (extChartAt 𝓘(ℝ,Model n) a).symm (Metric.closedBall z r))
    (hCb : LipschitzOnWith Cb (extChartAt 𝓘(ℝ,Model n) b) T)
    (hφ : ContinuousOn φ (Metric.closedBall z r))
    (hz : u ((extChartAt 𝓘(ℝ,Model n) a).symm z)=φ z)
    (hgap : ∀ w∈Metric.closedBall z r,
      ε*dist w z^2≤u ((extChartAt 𝓘(ℝ,Model n) a).symm w)-φ w)
    (hSregion : ∀ w∈Metric.ball z r,
      S w∈(extChartAt 𝓘(ℝ,Model n) b).target ∧
        (extChartAt 𝓘(ℝ,Model n) b).symm (S w)∈T)
    (hmountain : ∀ w∈Metric.ball z r, ∀ q∈Metric.closedBall z r,
      φ w+cost ((extChartAt 𝓘(ℝ,Model n) a).symm w)
        ((extChartAt 𝓘(ℝ,Model n) b).symm (S w)) ≤
      φ q+cost ((extChartAt 𝓘(ℝ,Model n) a).symm q)
        ((extChartAt 𝓘(ℝ,Model n) b).symm (S w)))
    (hS : HasStrictFDerivAt S J z) : |J.det| ≤ (cap/lam)*((Cb:ℝ)*(Da:ℝ))^n := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let ψ := extChartAt 𝓘(ℝ,Model n) b
  let C := (cap/lam)*((Cb:ℝ)*(Da:ℝ))^n
  have hC : 0 ≤ C := by dsimp only [C] <;> positivity
  have hχ : ContinuousOn χ.symm (Metric.closedBall z r) :=
    (continuousOn_extChartAt_symm a).mono hchart
  apply lower_test_abs_det_le (metricVolume n) hr hε hC
    (u.continuous.comp_continuousOn hχ) hφ
    (fun y => (continuous_cost_left (ψ.symm y)).comp_continuousOn hχ) hz hgap
    (R := chartContactRelation a b u v T) ?_ hmountain ?_ hS
  · intro w hw q hq hlocal
    exact ⟨(hSregion q hq).1,(hSregion q hq).2,
      hmtw.chart_local_contact_global u.continuous v.continuous hdual
        (hchart (Metric.ball_subset_closedBall hw)) hlocal⟩
  · intro A hA hAball
    have HA := chartContactRelation_volume_upper hlam hrho0 hrho1 hdual hmin hA
      (fun w hw => hchart (Metric.ball_subset_closedBall (hAball hw)))
      (hDa.mono (fun w hw => Metric.ball_subset_closedBall (hAball hw))) hCb
    have heq : ENNReal.ofReal lam*ENNReal.ofReal C=
        ENNReal.ofReal cap*((Cb:ℝ≥0∞)*(Da:ℝ≥0∞))^n := by
      rw [←ENNReal.ofReal_mul hlam.le]
      have H : lam*C=cap*((Cb:ℝ)*(Da:ℝ))^n := by dsimp only [C]; field_simp
      rw [H,ENNReal.ofReal_mul hcap,ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_coe_nnreal]
    apply (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_ne_zero_iff.mpr hlam)
      ENNReal.ofReal_ne_top).mp
    rw [←heq] at HA
    simpa only [mul_assoc,mul_left_comm,mul_comm] using HA

end ActualLowerTestBound
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_ChartLipschitz
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.WeakMTWTransport.metricVolume_model_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

lemma chart_spray_hasDerivAt (a : M) (z : TangentBundle 𝓘(ℝ,Model n) M) {t : ℝ}
    (ht : (sprayFlow t z).1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    HasDerivAt (fun s => extChartAt 𝓘(ℝ,Model n) a (sprayFlow s z).1)
      (mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) (extChartAt 𝓘(ℝ,Model n) a)
        (sprayFlow t z).1 (sprayFlow t z).2) t := by
  have hsrc : (sprayFlow t z).1∈(chartAt (Model n) a).source := by
    simpa only [extChartAt_source] using ht
  have projectedDeriv :=
    (ContinuousLinearMap.fst ℝ (Model n) (Model n)).hasFDerivAt.comp_hasDerivAt t
      (sprayFlow_chart_hasDerivAt (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) z ht)
  change HasDerivAt (fun s => extChartAt 𝓘(ℝ,Model n) a (sprayFlow s z).1)
    (tangentCoordChange 𝓘(ℝ,Model n) (sprayFlow t z).1 a
      (sprayFlow t z).1 (sprayFlow t z).2) t at projectedDeriv
  apply projectedDeriv.congr_deriv
  symm
  change (mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) (chartAt (Model n) a)
    (sprayFlow t z).1) (sprayFlow t z).2 = _
  rw [mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

variable [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_lipschitzOn_chart (a : M) :
    ∃ C : ℝ≥0, ∃ r>0, ball a r⊆(extChartAt 𝓘(ℝ,Model n) a).source ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a) (ball a r) := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨C,hC,H⟩ := eventually_norm_mfderiv_extChartAt_lt 𝓘(ℝ,Model n) a
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a) H)
  let Cnn : ℝ≥0 := ⟨C,hC.le⟩
  refine ⟨Cnn,R/3,by positivity,?_,?_⟩
  · exact fun x hx => (hsub ((ball_subset_ball (by linarith : R/3≤R)) hx)).1
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  obtain ⟨p,hp,he⟩ := exists_minimizing_vector (n := n) x y
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  have hpN : ‖p‖=dist x y := by rw [←he]; exact hp.symm
  have hpath : ∀ t∈Icc (0:ℝ) 1, (sprayFlow t z).1∈ball a R := by
    intro t ht
    have hD := dist_sprayFlow_le z 0 t
    simp only [sprayFlow_zero,zero_sub,abs_neg,abs_of_nonneg ht.1] at hD
    change dist x (sprayFlow t z).1≤t*‖p‖ at hD
    have hD' : dist x (sprayFlow t z).1≤dist x y :=
      hD.trans (by rw [←hpN]; exact mul_le_of_le_one_left (norm_nonneg _) ht.2)
    have hxy := dist_triangle x a y
    have hax : dist x a<R/3 := hx
    have hay : dist y a<R/3 := hy
    have htri := dist_triangle (sprayFlow t z).1 x a
    rw [dist_comm (sprayFlow t z).1 x] at htri
    rw [dist_comm a y] at hxy
    change dist (sprayFlow t z).1 a<R
    linarith
  let γ := fun t : ℝ => extChartAt 𝓘(ℝ,Model n) a (sprayFlow t z).1
  let dγ : ℝ → Model n := fun t => mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n)
    (extChartAt 𝓘(ℝ,Model n) a) (sprayFlow t z).1 (sprayFlow t z).2
  have hd : ∀ t∈Icc (0:ℝ) 1, HasDerivWithinAt γ (dγ t) (Icc 0 1) t := by
    intro t ht
    exact (chart_spray_hasDerivAt a z (hsub (hpath t ht)).1).hasDerivWithinAt
  have hb : ∀ t∈Icc (0:ℝ) 1, ‖dγ t‖≤C*‖p‖ := by
    intro t ht
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    rw [sprayFlow_speed]
    exact mul_le_mul_of_nonneg_right (hsub (hpath t ht)).2.le (norm_nonneg _)
  have hfin := norm_image_sub_le_of_norm_deriv_le_segment_01' hd (fun t ht => hb t ⟨ht.1,ht.2.le⟩)
  have he1 : (sprayFlow 1 z).1=y := by
    simpa only [z,←riemannianExp_eq_sprayFlow] using he
  have he0 : (sprayFlow 0 z).1=x := by rw [sprayFlow_zero]
  change dist (extChartAt 𝓘(ℝ,Model n) a x) (extChartAt 𝓘(ℝ,Model n) a y)≤C*dist x y
  simpa only [γ,he1,he0,←dist_eq_norm,dist_comm,hpN] using hfin

end WeakMTWTransport

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

variable [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
lemma densityDualClass_isDual {vol : Measure M} {lam cap : ℝ} {x0 : M}
    {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)} (h : uv ∈ densityDualClass vol lam cap x0) :
    IsCostDualPair uv.1 uv.2 := by
  constructor
  · exact congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.1.2.1.symm
  · exact congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.1.2.2.symm

end SectionOscillation

open Filter

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_SmoothTestPDE
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section SmoothTestPDE
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma chartTestContact_contDiffAt {a b : M} {z : Model n} {φ : Model n → ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hb : coordinateBackward a (-1,z,fderiv ℝ φ z)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    ContDiffAt ℝ 1 (chartTestContact a b φ) z := by
  have hA : ContDiffAt ℝ 1 (coordinateContact a b) (z,fderiv ℝ φ z) :=
    (coordinateContact_contDiffAt (a := a) (b := b) (q := (z,fderiv ℝ φ z)) hz hb).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hB : ContDiffAt ℝ 1 (fun w : Model n => (w,fderiv ℝ φ w)) z :=
    contDiffAt_id.prodMk (hφ.fderiv_right (m := 1) (by norm_num))
  exact hA.comp (f := fun w : Model n => (w,fderiv ℝ φ w)) z hB

end SmoothTestPDE
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_LocalUniformTestPDE
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section LocalUniformTestPDE
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

variable [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_locally_uniform_test_det_bound_oai
    (hmtw : WeakMTW (n := n) (M := M)) {lam cap : ℝ}
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (a b : M) :
    ∃ U : Set (Model n), IsOpen U ∧ extChartAt 𝓘(ℝ,Model n) a a∈U ∧
    ∃ V : Set M, IsOpen V ∧ b∈V ∧
    ∃ K≥0, ∀ z∈U, ∀ (x0:M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ φ : Model n → ℝ, ContDiffAt ℝ 2 φ z →
      coordinateBackward a (-1,z,fderiv ℝ φ z)∈V →
      chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
        ((extChartAt 𝓘(ℝ,Model n) a).symm z) →
      uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)=φ z →
      (∃ ε>0,∀ᶠ w in 𝓝 z,ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-φ w) →
      (∃ m>0,∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d) →
      |(fderiv ℝ (chartTestContact a b φ) z).det|≤K := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let ψ := extChartAt 𝓘(ℝ,Model n) b
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨Da,r₁,hr₁,hchart₁,hDa⟩ := exists_lipschitzOn_inverse_chart (E := Model n) a
  obtain ⟨Cb,R,hR,hT,hCb⟩ := exists_lipschitzOn_chart (n := n) b
  let U := Metric.ball (χ a) r₁
  let V := Metric.ball b R
  let K := (cap/lam)*((Cb:ℝ)*(Da:ℝ))^n
  refine ⟨U,Metric.isOpen_ball,Metric.mem_ball_self hr₁,V,Metric.isOpen_ball,
    Metric.mem_ball_self hR,K,by dsimp [K] <;> positivity,?_⟩
  intro z hz x0 uv huv φ hφ hYz hpφ hval hgap hpos
  have hzT : z∈χ.target := hchart₁ hz
  obtain ⟨ε,hε,hgap⟩ := hgap
  obtain ⟨m,hm,hpos⟩ := hpos
  obtain ⟨r₂,hr₂,_,hmount⟩ := exists_test_mountains hzT hφ hpφ hm hpos
  let Y := fun w : Model n => coordinateBackward a (-1,w,fderiv ℝ φ w)
  have hY : ContinuousAt Y z :=
    (coordinateBackward_contMDiffAt (q := (-1,z,fderiv ℝ φ z)) hzT).continuousAt.comp
      (x := z) (f := fun w : Model n => ((-1:ℝ),w,fderiv ℝ φ w))
      (continuousAt_const.prodMk (continuousAt_id.prodMk
        (hφ.fderiv_right (m := 1) (by norm_num)).continuousAt))
  have hYn : ∀ᶠ w : Model n in 𝓝 z,Y w∈V :=
    hY.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hYz)
  have hnear : ∀ᶠ w : Model n in 𝓝 z,
      ε*dist w z^2≤uv.1 (χ.symm w)-φ w ∧
      w∈U ∧ w∈Metric.ball z r₂ ∧ ContinuousAt φ w ∧ Y w∈V := by
    filter_upwards [hgap,Metric.isOpen_ball.mem_nhds hz,Metric.ball_mem_nhds z hr₂,
      hφ.eventually (by norm_num),hYn] with w hw h₁ h₂ hφw hYw
    exact ⟨hw,h₁,h₂,hφw.continuousAt,hYw⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  obtain ⟨rho0,rho1,hrho0,hrho1,hmin⟩ := huv.2
  apply hmtw.lower_test_chart_det_bound hlam hcap hrho0 hrho1
    (densityDualClass_isDual huv) hmin hr hε
    (fun w hw => hchart₁ (hrsub hw).2.1)
    (hDa.mono (fun w hw => (hrsub hw).2.1)) hCb
    (fun w hw => (hrsub hw).2.2.2.1.continuousWithinAt)
    hval (fun w hw => (hrsub hw).1) (S := chartTestContact a b φ) ?_ ?_
    ((chartTestContact_contDiffAt hzT hφ (hT hYz)).hasStrictFDerivAt (by norm_num))
  · intro w hw
    have hy : Y w∈ψ.source := hT (hrsub (Metric.ball_subset_closedBall hw)).2.2.2.2
    refine ⟨ψ.map_source hy,?_⟩
    change ψ.symm (ψ (Y w))∈Metric.ball b R
    rw [ψ.left_inv hy]
    exact (hrsub (Metric.ball_subset_closedBall hw)).2.2.2.2
  · intro w hw q hq
    have hy : Y w∈ψ.source := hT (hrsub (Metric.ball_subset_closedBall hw)).2.2.2.2
    change φ w+cost (χ.symm w) (ψ.symm (ψ (Y w)))≤φ q+cost (χ.symm q) (ψ.symm (ψ (Y w)))
    rw [ψ.left_inv hy]
    exact hmount w (Metric.ball_subset_closedBall (hrsub (Metric.ball_subset_closedBall hw)).2.2.1)
      q (Metric.ball_subset_closedBall (hrsub hq).2.2.1)

end LocalUniformTestPDE
end WeakMTWTransport

end

end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.exists_locally_uniform_test_det_bound_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.exists_locally_uniform_test_det_bound_oai.{u_1}
