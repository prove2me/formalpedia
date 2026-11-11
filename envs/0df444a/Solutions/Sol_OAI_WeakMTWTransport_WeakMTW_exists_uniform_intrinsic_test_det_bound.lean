-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.exists_uniform_intrinsic_test_det_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:03.337933+00:00
-- url     : https://prove2.me/submissions/18677b93-a8f9-4382-bff2-0837131fa885

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
import Definitions.Def_OAIQ232A027
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_test_det_bound_on_charts
import Theorems.Thm_OAI_WeakMTWTransport_mixed_intrinsic_det
import Theorems.Thm_OAI_WeakMTWTransport_normal_test_to_chart

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_ChartLipschitz
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

variable [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma contact_stationarity_eventually {a b : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (ha : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : chartGradientVector a q.1 q.2∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1))
    (hb : coordinateBackward a (-1,q.1,q.2)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    ∀ᶠ q' in 𝓝 q, chartCostCovector a b (q'.1,coordinateContact a b q')= -q'.2 := by
  have hY : ContinuousAt (fun q : Model n×(Model n →L[ℝ] ℝ) => coordinateBackward a (-1,q.1,q.2)) q :=
    (coordinateBackward_contMDiffAt (q := (-1,q.1,q.2)) ha).continuousAt.comp
      (x := q) (continuousAt_const.prodMk continuousAt_id)
  have hT := hY.preimage_mem_nhds ((isOpen_extChartAt_source b).mem_nhds hb)
  have hA := continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target a).mem_nhds ha)
  filter_upwards [hT,hA,chartGradientVector_regular_near ha hp] with q' hb' ha' hp'
  dsimp only [chartCostCovector,coordinateContact]
  rw [(extChartAt 𝓘(ℝ,Model n) b).left_inv hb']
  exact (chartCost_gradient_at_contact ha' hp').fderiv

end ContactStationarity
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Charts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section Charts
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_bilipschitz_chart (a : M) :
    ∃ C D : ℝ≥0, ∃ r>0, ball a r⊆(extChartAt 𝓘(ℝ,Model n) a).source ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a) (ball a r) ∧
      LipschitzOnWith D (extChartAt 𝓘(ℝ,Model n) a).symm
        (extChartAt 𝓘(ℝ,Model n) a '' ball a r) := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨C,r,hr,hs,hC⟩ := exists_lipschitzOn_chart (n := n) a
  obtain ⟨D,s,hspos,_,hD⟩ := exists_lipschitzOn_inverse_chart (E := Model n) a
  obtain ⟨t,ht,htsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (ball_mem_nhds a hr) ((continuousAt_extChartAt (I := 𝓘(ℝ,Model n)) a).preimage_mem_nhds
      (ball_mem_nhds _ hspos)))
  refine ⟨C,D,t,ht,fun x hx => hs (htsub hx).1,hC.mono (fun x hx => (htsub hx).1),?_⟩
  apply hD.mono
  rintro z ⟨x,hx,rfl⟩
  exact (htsub hx).2

end Charts
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ContactStationarity
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
section ContactStationarity
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma chartTestContact_relative_hessian_fixed {a b : M} {z : Model n} {φ : Model n → ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hp : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z))
    (hb : coordinateBackward a (-1,z,fderiv ℝ φ z)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    let c := coordinateBackward a (-1,z,fderiv ℝ φ z)
    let y := extChartAt 𝓘(ℝ,Model n) b c
    let D := fderiv ℝ (chartCostCovector a b) (z,y)
    fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a c)) z =
      -((D.comp (ContinuousLinearMap.inr ℝ (Model n) (Model n))).comp
        (fderiv ℝ (chartTestContact a b φ) z)) := by
  dsimp only
  let c := coordinateBackward a (-1,z,fderiv ℝ φ z)
  let y := extChartAt 𝓘(ℝ,Model n) b c
  let G := chartCostCovector (n := n) a b
  let T := chartTestContact a b φ
  have hTy : T z=y := rfl
  have hy : y∈(extChartAt 𝓘(ℝ,Model n) b).target :=
    (extChartAt 𝓘(ℝ,Model n) b).map_source hb
  have hyb : (extChartAt 𝓘(ℝ,Model n) b).symm y=c :=
    (extChartAt 𝓘(ℝ,Model n) b).left_inv hb
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,chartGradientVector a z (fderiv ℝ φ z)⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) ((extChartAt 𝓘(ℝ,Model n) a).symm z,
        (extChartAt 𝓘(ℝ,Model n) b).symm y) := by
    rw [hyb,show c=riemannianExp _ (chartGradientVector a z (fderiv ℝ φ z)) from
      coordinateBackward_eq_exp_chartGradient hz _]
    exact hc
  have hG : DifferentiableAt ℝ G (z,y) :=
    (chartCostCovector_contDiffAt hz hy hc').differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hT : DifferentiableAt ℝ T z :=
    (chartTestContact_contDiffAt hz hφ hb).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hgraph : HasFDerivAt (fun w => (w,T w))
      ((ContinuousLinearMap.id ℝ (Model n)).prod (fderiv ℝ T z)) z :=
    (hasFDerivAt_id z).prodMk hT.hasFDerivAt
  have hggraph := hG.hasFDerivAt.comp z hgraph
  have he : (fun w => G (w,T w))=ᶠ[𝓝 z] (fun w => -fderiv ℝ φ w) := by
    have hZ : ContinuousAt (fun w => (w,fderiv ℝ φ w)) z :=
      continuousAt_id.prodMk (hφ.fderiv_right (m := 1) (by norm_num)).continuousAt
    exact hZ.eventually (contact_stationarity_eventually hz hp hb)
  have heD := (hggraph.congr_of_eventuallyEq he.symm).unique
    (((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.neg)
  have hbaseMap : HasFDerivAt (fun w : Model n => (w,y))
      ((ContinuousLinearMap.id ℝ (Model n)).prod 0) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const y z)
  have hbase := hG.hasFDerivAt.comp (f := fun w : Model n => (w,y)) z hbaseMap
  have hbaseEq : (fun w => G (w,y))=fderiv ℝ (chartCost a c) := by
    funext w
    change fderiv ℝ (chartCost a ((extChartAt 𝓘(ℝ,Model n) b).symm y)) w = _
    rw [hyb]
  change HasFDerivAt (fun w => G (w,y)) _ z at hbase
  rw [hbaseEq] at hbase
  have hbaseD := hbase.fderiv
  ext ξ η
  have heV := congrArg (fun A : Model n →L[ℝ] Model n →L[ℝ] ℝ => A ξ η) heD
  have hbV := congrArg (fun A : Model n →L[ℝ] Model n →L[ℝ] ℝ => A ξ η) hbaseD
  dsimp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,zero_apply,
    neg_apply,Pi.neg_apply] at heV hbV
  have hsplit : (ξ,fderiv ℝ T z ξ)=(ξ,(0:Model n))+(0,fderiv ℝ T z ξ) := by simp
  rw [hsplit,map_add,add_apply] at heV
  change fderiv ℝ (fderiv ℝ φ) z ξ η+fderiv ℝ (fderiv ℝ (chartCost a c)) z ξ η =
    -fderiv ℝ G (z,y) (0,fderiv ℝ T z ξ) η
  simp only [neg_apply,zero_apply] at heV hbV
  linarith only [heV,hbV]

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
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

lemma matrix_norm_det_le_factorial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {R : ℝ} (hR : 0≤R) (hA : ∀ i j, ‖A i j‖≤R) :
    ‖A.det‖≤(Fintype.card ι).factorial*R^(Fintype.card ι) := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, R^(Fintype.card ι) := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [norm_units_zsmul,norm_prod]
      calc
        _ ≤ ∏ _i : ι, |R| := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun index _ => (hA (σ index) index).trans (le_abs_self R))
        _ = _ := by simp [abs_of_nonneg hR]
    _ = _ := by simp [Fintype.card_perm]

lemma normDet_le_factorial_opNorm {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (F : U →L[ℝ] V) (hd : Module.finrank ℝ U=Module.finrank ℝ V) :
    F.toLinearMap.normDet≤(Module.finrank ℝ U).factorial*‖F‖^(Module.finrank ℝ U) := by
  classical
  let b := stdOrthonormalBasis ℝ U
  let d : OrthonormalBasis (Fin (finrank ℝ U)) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (finCongr hd).symm
  rw [LinearMap.normDet_eq_norm_det_toMatrix F.toLinearMap b d]
  have hA : ∀ i j, ‖(F.toLinearMap.toMatrix b.toBasis d.toBasis) i j‖≤‖F‖ := by
    intro i j
    rw [LinearMap.toMatrix_apply,d.coe_toBasis_repr_apply]
    change ‖d.repr (F (b j)) i‖≤‖F‖
    rw [d.repr_apply_apply]
    calc
      _ ≤ ‖d i‖*‖F (b j)‖ := norm_inner_le_norm _ _
      _ = ‖F (b j)‖ := by rw [d.orthonormal.norm_eq_one i,one_mul]
      _ ≤ ‖F‖*‖b j‖ := F.le_opNorm _
      _ = ‖F‖ := by rw [b.orthonormal.norm_eq_one,mul_one]
  simpa only [Fintype.card_fin] using matrix_norm_det_le_factorial
    (F.toLinearMap.toMatrix b.toBasis d.toBasis) (norm_nonneg F) hA

end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_RelativeHessianBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section LocalUniformRelativeHessian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma relative_hessian_operator_factor_fixed {a b : M} {z : Model n} {φ : Model n → ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hp : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z))
    (hb : coordinateBackward a (-1,z,fderiv ℝ φ z)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    let c := coordinateBackward a (-1,z,fderiv ℝ φ z)
    bilinearOperator (fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a c)) z) =
      (mixedCostOperator a b z (extChartAt 𝓘(ℝ,Model n) b c)).comp
        (fderiv ℝ (chartTestContact a b φ) z) := by
  dsimp only
  rw [chartTestContact_relative_hessian_fixed hz hφ hp hb]
  apply ContinuousLinearMap.ext
  intro d
  apply ext_inner_right ℝ
  intro e
  simp only [ContinuousLinearMap.comp_apply,bilinearOperator_inner,mixedCostOperator,
    neg_apply]

end LocalUniformRelativeHessian
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_IntrinsicJacobian
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

local instance inverseChartNormedAddCommGroup_re40db9_1 (y : Model n) (x : M) : NormedAddCommGroup
    (TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance inverseChartNormedSpace_re40db9_1 (y : Model n) (x : M) : NormedSpace ℝ
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

omit [CompactSpace M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma eventually_chartJacobian_bounds (a : M) :
    ∃ l u : ℝ, 0<l ∧ 0<u ∧ ∀ᶠ x in 𝓝 a,
      l ≤ chartJacobian (n := n) a x ∧ chartJacobian (n := n) a x≤u := by
  let d := extChartAt 𝓘(ℝ,Model n) a
  have : IsContinuousRiemannianBundle (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨C,hC,hCd⟩ := eventually_norm_mfderiv_extChartAt_lt 𝓘(ℝ,Model n) a
  obtain ⟨D,hD,hDi⟩ := eventually_norm_mfderivWithin_symm_extChartAt_comp_lt 𝓘(ℝ,Model n) a
  let N := Module.finrank ℝ (Model n)
  let U : ℝ := N.factorial * C ^ N
  let Q : ℝ := N.factorial * D ^ N
  have hU : 0<U := mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos hC _)
  have hQ : 0<Q := mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos hD _)
  refine ⟨Q⁻¹,U,inv_pos.mpr hQ,hU,?_⟩
  filter_upwards [hCd,hDi,extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a] with x hxC hxD hxs
  let F : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d x
  let G : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (d.symm (d x)) :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d.symm (d x)
  have hF : ‖F‖≤C := hxC.le
  have hG : ‖G‖≤D := by
    simp only [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at hxD
    exact hxD.le
  have hFU : F.toLinearMap.normDet≤U :=
    (normDet_le_factorial_opNorm F rfl).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hF _) (Nat.cast_nonneg _))
  have hGQ : G.toLinearMap.normDet≤Q :=
    (normDet_le_factorial_opNorm G rfl).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hG _) (Nat.cast_nonneg _))
  have hp := chartJacobian_inverse_product a (d.map_source hxs)
  rw [d.left_inv hxs] at hp
  refine ⟨?_,hFU⟩
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hQ).mpr
  calc
    1=chartJacobian (n := n) a x*G.toLinearMap.normDet := hp.symm
    _ ≤ chartJacobian (n := n) a x*Q := mul_le_mul_of_nonneg_left hGQ (chartJacobian_nonneg a x)

end ChartJacobianBounds
end WeakMTWTransport

end

end

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

end PullbackDet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_UniformCharts
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
open Set Filter Manifold Bundle Module Metric
open scoped Topology ContDiff BigOperators NNReal

namespace WeakMTWTransport
section UniformCharts
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_uniform_volume_charts :
    ∃ C : ℝ≥0, 0<C ∧ ∃ l u : ℝ, 0<l ∧ 0<u ∧ ∀ x : M,
      ∃ a : M, ∃ U : Set M, IsOpen U ∧ x∈U ∧
        U⊆(extChartAt 𝓘(ℝ,Model n) a).source ∧
        LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a) U ∧
        LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a).symm
          ((extChartAt 𝓘(ℝ,Model n) a) '' U) ∧
        ∀ z∈U, l ≤ chartJacobian (n := n) a z ∧ chartJacobian (n := n) a z≤u := by
  classical
  have H (x : M) : ∃ C D : ℝ≥0, ∃ l u : ℝ, 0<l ∧ 0<u ∧
      ∃ U : Set M, IsOpen U ∧ x∈U ∧ U⊆(extChartAt 𝓘(ℝ,Model n) x).source ∧
        LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) x) U ∧
        LipschitzOnWith D (extChartAt 𝓘(ℝ,Model n) x).symm
          ((extChartAt 𝓘(ℝ,Model n) x) '' U) ∧
        ∀ z∈U, l ≤ chartJacobian (n := n) x z ∧ chartJacobian (n := n) x z≤u := by
    obtain ⟨C,D,r,hr,hUs,hd,hdi⟩ := exists_bilipschitz_chart (n := n) x
    let U := ball x r
    have hUo : IsOpen U := isOpen_ball
    have hxU : x∈U := mem_ball_self hr
    obtain ⟨l,u,hl,hu,hnear⟩ := eventually_chartJacobian_bounds (n := n) x
    obtain ⟨V,hVs,hVo,hxV⟩ := _root_.mem_nhds_iff.mp hnear
    exact ⟨C,D,l,u,hl,hu,U∩V,hUo.inter hVo,⟨hxU,hxV⟩,
      inter_subset_left.trans hUs,hd.mono inter_subset_left,
      hdi.mono (image_mono inter_subset_left),fun z hz => hVs hz.2⟩
  choose C D l u hl hu U hUo hxU hUs hd hdi hj using H
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hUo
    (show univ⊆⋃ x, U x from fun x _ => mem_iUnion.mpr ⟨x,hxU x⟩)
  let C0 : ℝ≥0 := 1+∑ a∈s, (C a+D a)
  let R : ℝ := 1+∑ a∈s, (l a)⁻¹
  let u0 : ℝ := 1+∑ a∈s, u a
  have hC0 : 0<C0 := by dsimp [C0] <;> positivity
  have hR : 0<R := by
    have := Finset.sum_nonneg (fun a (_ : a∈s) => (inv_pos.mpr (hl a)).le)
    dsimp [R]
    linarith
  have hu0 : 0<u0 := by
    have := Finset.sum_nonneg (fun a (_ : a∈s) => (hu a).le)
    dsimp [u0]
    linarith
  refine ⟨C0,hC0,R⁻¹,u0,inv_pos.mpr hR,hu0,?_⟩
  intro x
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  have hCD : C a+D a≤C0 := by
    have h := Finset.single_le_sum (f := fun a => C a+D a) (fun _ _ => zero_le) ha
    exact h.trans (le_add_of_nonneg_left (by positivity))
  have hCa : C a≤C0 := (le_add_of_nonneg_right (zero_le)).trans hCD
  have hDa : D a≤C0 := (le_add_of_nonneg_left (zero_le)).trans hCD
  have hla : (l a)⁻¹≤R := by
    have h := Finset.single_le_sum (fun b (_ : b∈s) => (inv_pos.mpr (hl b)).le) ha
    dsimp [R]
    linarith
  have hlower : R⁻¹≤l a := by
    have h := (inv_le_inv₀ hR (inv_pos.mpr (hl a))).mpr hla
    simpa only [inv_inv] using h
  have hua : u a≤u0 := by
    have h := Finset.single_le_sum (fun b (_ : b∈s) => (hu b).le) ha
    dsimp [u0]
    linarith
  exact ⟨a,U a,hUo a,hxa,hUs a,(hd a).weaken hCa,(hdi a).weaken hDa,
    fun z hz => ⟨hlower.trans (hj a z hz).1,((hj a z hz).2).trans hua⟩⟩

end UniformCharts
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_IntrinsicTestDet
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction NNReal

namespace WeakMTWTransport
section IntrinsicTestDet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.ivFinite
lemma WeakMTW.exists_uniform_intrinsic_test_det_bound_oai
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ}
    (hlam:0<lam) (hcap:0 ≤ cap) :
    ∃ K:ℝ,0<K ∧ ∀ (x0 x:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ))
      (p:TangentSpace 𝓘(ℝ,Model n) x) (φ:TangentSpace 𝓘(ℝ,Model n) x → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → p∈injectivityDomain x →
      ContDiffAt ℝ 2 φ 0 → fderiv ℝ φ 0=innerSL ℝ p →
      uv.1 x=φ 0 → (∀ᶠ w in 𝓝 0,φ w≤uv.1 (riemannianExp x w)) →
      (∃m>0,∀d,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue x p d) →
      expJacobian (n:=n) x p *
        |(bilinearOperator (fderiv ℝ (fderiv ℝ φ) 0+normalHessian x p)).det|≤K := by
  obtain ⟨C,hC,l,u,hl,hu,Hcharts⟩:=exists_uniform_volume_charts (n:=n) (M:=M)
  let A:ℝ:=(cap/lam)*((C:ℝ)*(C:ℝ))^n
  have hA:0≤A:=by dsimp [A] <;> positivity
  refine ⟨u*A/l+1,by positivity,?_⟩
  intro x0 x uv p φ huv hp hφ hφD hval hlo hpos
  let y:=riemannianExp (n:=n) x p
  obtain ⟨a,U,hU,hxU,hUa,hCa,hDa,hJa⟩:=Hcharts x
  obtain ⟨b,V,hV,hyV,hVb,hCb,hDb,hJb⟩:=Hcharts y
  have hx:=hUa hxU
  have hy:=hVb hyV
  let z:=extChartAt 𝓘(ℝ,Model n) a x
  obtain ⟨ψ,R,hψ,hreg,hey,hvalue,hlower,hpositive,hR,hpull⟩:=
    normal_test_to_chart hx hp hφ hφD hval hlo hpos
  have Hbound:|(fderiv ℝ (chartTestContact a b ψ) z).det|≤A:=by
    apply hmtw.test_det_bound_on_charts hlam hcap hU hUa hV hVb hDa hCb
      (mem_image_of_mem _ hxU) huv hψ (by rwa [hey]) hreg hvalue hlower
    simpa only [hey] using hpositive
  let W:=bilinearOperator (fderiv ℝ (fderiv ℝ φ) 0+normalHessian x p)
  let B:=mixedCostOperator a b z (extChartAt 𝓘(ℝ,Model n) b y)
  let T:=fderiv ℝ (chartTestContact a b ψ) z
  have hfactor:(R.adjoint.comp (W.comp R))=B.comp T:=by
    rw [←hpull]
    have H:=relative_hessian_operator_factor_fixed ((extChartAt 𝓘(ℝ,Model n) a).map_source hx)
      hψ hreg (by rwa [hey])
    simpa only [hey] using H
  have Hdet:R.toLinearMap.normDet^2* |W.det|=|B.det| * |T.det|:=by
    rw [←abs_det_hessian_pullback R W rfl,hfactor]
    change |(B.toLinearMap.comp T.toLinearMap).det|=_
    rw [LinearMap.det_comp,abs_mul]
  have Hmix:chartJacobian (n:=n) a x * |B.det| *
      (chartJacobian (n:=n) b y*expJacobian (n:=n) x p)=1:=mixed_intrinsic_det hx hp hy
  have Heq:chartJacobian (n:=n) b y*expJacobian (n:=n) x p* |W.det|=
      chartJacobian (n:=n) a x* |T.det|:=by
    calc
      _ = (chartJacobian (n:=n) a x*R.toLinearMap.normDet)^2*
          (chartJacobian (n:=n) b y*expJacobian (n:=n) x p* |W.det|):=by rw [hR]; ring
      _ = (chartJacobian (n:=n) a x)^2*(chartJacobian (n:=n) b y*expJacobian (n:=n) x p)*
          (R.toLinearMap.normDet^2* |W.det|):=by ring
      _ = (chartJacobian (n:=n) a x)^2*(chartJacobian (n:=n) b y*expJacobian (n:=n) x p)*
          (|B.det| * |T.det|):=by rw [Hdet]
      _ = chartJacobian (n:=n) a x*(chartJacobian (n:=n) a x* |B.det| *
          (chartJacobian (n:=n) b y*expJacobian (n:=n) x p))* |T.det|:=by ring
      _ = _:=by rw [Hmix]; ring
  have Hlo:l*(expJacobian (n:=n) x p* |W.det|)≤
      chartJacobian (n:=n) b y*expJacobian (n:=n) x p* |W.det|:=by
    nlinarith only [mul_le_mul_of_nonneg_right (hJb y hyV).1
      (mul_nonneg (expJacobian_pos_of_injectivityDomain hp).le (abs_nonneg W.det))]
  have Hhi:chartJacobian (n:=n) a x* |T.det|≤u*A:=
    mul_le_mul (hJa x hxU).2 Hbound (abs_nonneg _) hu.le
  have H:expJacobian (n:=n) x p* |W.det|≤u*A/l:=
    (le_div_iff₀ hl).mpr (by nlinarith only [Hlo,Heq,Hhi])
  exact H.trans (by linarith)

end IntrinsicTestDet
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.exists_uniform_intrinsic_test_det_bound_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.exists_uniform_intrinsic_test_det_bound_oai.{u_1}
