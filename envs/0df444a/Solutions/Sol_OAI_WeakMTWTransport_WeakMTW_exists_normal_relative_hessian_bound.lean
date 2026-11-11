-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.exists_normal_relative_hessian_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:38.900306+00:00
-- url     : https://prove2.me/submissions/7353806b-e8a3-4bd0-89ab-c72b4709e0ca

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
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_strict_test_det_bound

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_JetPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

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

lemma chartTestContact_relative_hessian {a : M} {z : Model n} {φ : Model n → ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hp : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z)) :
    let b := coordinateBackward a (-1,z,fderiv ℝ φ z)
    let y := extChartAt 𝓘(ℝ,Model n) b b
    let D := fderiv ℝ (chartCostCovector a b) (z,y)
    fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a b)) z =
      -((D.comp (ContinuousLinearMap.inr ℝ (Model n) (Model n))).comp
        (fderiv ℝ (chartTestContact a b φ) z)) := by
  dsimp only
  let b := coordinateBackward a (-1,z,fderiv ℝ φ z)
  let y := extChartAt 𝓘(ℝ,Model n) b b
  let G := chartCostCovector (n := n) a b
  let T := chartTestContact a b φ
  have hTy : T z=y := rfl
  have hy : y∈(extChartAt 𝓘(ℝ,Model n) b).target :=
    (extChartAt 𝓘(ℝ,Model n) b).map_source (mem_extChartAt_source b)
  have hyb : (extChartAt 𝓘(ℝ,Model n) b).symm y=b :=
    (extChartAt 𝓘(ℝ,Model n) b).left_inv (mem_extChartAt_source b)
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,chartGradientVector a z (fderiv ℝ φ z)⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) ((extChartAt 𝓘(ℝ,Model n) a).symm z,
        (extChartAt 𝓘(ℝ,Model n) b).symm y) := by
    rw [hyb,show b=riemannianExp _ (chartGradientVector a z (fderiv ℝ φ z)) from
      coordinateBackward_eq_exp_chartGradient hz _]
    exact hc
  have hG : DifferentiableAt ℝ G (z,y) :=
    (chartCostCovector_contDiffAt hz hy hc').differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hT : DifferentiableAt ℝ T z :=
    (chartTestContact_contDiffAt hz hφ (mem_extChartAt_source b)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hgraph : HasFDerivAt (fun w => (w,T w))
      ((ContinuousLinearMap.id ℝ (Model n)).prod (fderiv ℝ T z)) z :=
    (hasFDerivAt_id z).prodMk hT.hasFDerivAt
  have hggraph := hG.hasFDerivAt.comp z hgraph
  have he : (fun w => G (w,T w))=ᶠ[𝓝 z] (fun w => -fderiv ℝ φ w) := by
    have hZ : ContinuousAt (fun w => (w,fderiv ℝ φ w)) z :=
      continuousAt_id.prodMk (hφ.fderiv_right (m := 1) (by norm_num)).continuousAt
    exact hZ.eventually (contact_stationarity_eventually hz hp (mem_extChartAt_source b))
  have heD := (hggraph.congr_of_eventuallyEq he.symm).unique
    (((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.neg)
  have hbaseMap : HasFDerivAt (fun w : Model n => (w,y))
      ((ContinuousLinearMap.id ℝ (Model n)).prod 0) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const y z)
  have hbase := hG.hasFDerivAt.comp (f := fun w : Model n => (w,y)) z hbaseMap
  have hbaseEq : (fun w => G (w,y))=fderiv ℝ (chartCost a b) := by
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
  change fderiv ℝ (fderiv ℝ φ) z ξ η+fderiv ℝ (fderiv ℝ (chartCost a b)) z ξ η =
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinateTrueLog
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
section CoordinateTrueLog
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_chart_covector_for_log {a : M} {p : TangentSpace 𝓘(ℝ,Model n) a}
    (hp : p∈injectivityDomain a) :
    let z := extChartAt 𝓘(ℝ,Model n) a a
    ∃ L : Model n →L[ℝ] ℝ,
      chartGradientVector a z L∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
      coordinateBackward a (-1,z,L)=riemannianExp a p ∧
      HasFDerivAt (chartCost a (riemannianExp a p)) (-L) z := by
  let : Nonempty M := ⟨a⟩
  let z := extChartAt 𝓘(ℝ,Model n) a a
  let A : TangentBundle 𝓘(ℝ,Model n) M := ⟨a,0⟩
  let P : TangentBundle 𝓘(ℝ,Model n) M := ⟨a,p⟩
  let c := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) A
  let L := riemannianCoordinateMetric a z (c P).2
  have hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hPs : P∈c.source := (tangent_chart_source_iff A P).mpr (mem_extChartAt_source a)
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
  have hex : coordinateBackward a (-1,z,L)=riemannianExp a p := by
    rw [coordinateBackward_eq_exp_chartGradient hz]
    exact congrArg (fun Q : TangentBundle 𝓘(ℝ,Model n) M => riemannianExp Q.1 Q.2) he
  refine ⟨L,hreg,hex,?_⟩
  rw [←hex]
  exact chartCost_gradient_at_contact hz hreg

end CoordinateTrueLog
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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CompactConorm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Module

namespace WeakMTWTransport
section NormDetBound
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

lemma norm_eigenvector_image_eq_singularValue (A : E →ₗ[ℝ] F)
    {n : ℕ} (hn : finrank ℝ E=n) (i : Fin n) :
    ‖A (A.isSymmetric_adjoint_comp_self.eigenvectorBasis hn i)‖=A.singularValues i := by
  let v := A.isSymmetric_adjoint_comp_self.eigenvectorBasis hn i
  have hv : ‖v‖=1 := (A.isSymmetric_adjoint_comp_self.eigenvectorBasis hn).norm_eq_one i
  have he : (A.adjoint.comp A) v=A.isSymmetric_adjoint_comp_self.eigenvalues hn i • v :=
    A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hn i
  have hsq : ‖A v‖^2=A.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
    rw [←real_inner_self_eq_norm_sq,←A.adjoint_inner_left v (A v)]
    change inner ℝ ((A.adjoint.comp A) v) v=_
    rw [he,real_inner_smul_left,real_inner_self_eq_norm_sq,hv]
    ring
  apply (sq_eq_sq₀ (norm_nonneg _) (A.singularValues_nonneg i)).mp
  rw [hsq,A.sq_singularValues_fin hn i]
end NormDetBound
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_NormDetCoercivity
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
open Module

namespace WeakMTWTransport
section NormDetCoercivity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

lemma singularValue_le_of_conorm_det (A : E →ₗ[ℝ] F) {b K : ℝ} (hb : 0<b)
    (hA : ∀ v,b*‖v‖≤‖A v‖) (hK : A.normDet≤K) (i : Fin (finrank ℝ E)) :
    A.singularValues i≤K/b^(finrank ℝ E-1) := by
  classical
  have H : ∀ j : Fin (finrank ℝ E),b≤A.singularValues j := by
    intro j
    have H := hA (A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl j)
    rw [(A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).norm_eq_one,mul_one,
      norm_eigenvector_image_eq_singularValue] at H
    exact H
  have hp := Finset.prod_le_prod (s := Finset.univ.erase i)
    (fun _ _ => hb.le) (fun index _ => H index)
  have hp' : b^(finrank ℝ E-1)≤∏ j∈Finset.univ.erase i,A.singularValues j := by
    simpa only [Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ,Fintype.card_fin] using hp
  apply (le_div_iff₀ (pow_pos hb _)).mpr
  calc
    A.singularValues i*b^(finrank ℝ E-1) ≤
        A.singularValues i*(∏ j∈Finset.univ.erase i,A.singularValues j) :=
      mul_le_mul_of_nonneg_left hp' (A.singularValues_nonneg i)
    _ = A.normDet := by
      rw [A.normDet_eq_prod_singularValues,←Fin.prod_univ_eq_prod_range]
      exact Finset.mul_prod_erase Finset.univ (fun j : Fin (finrank ℝ E) => A.singularValues j) (Finset.mem_univ i)
    _ ≤ K := hK

lemma norm_le_of_conorm_det (A : E →ₗ[ℝ] F) {b K : ℝ} (hb : 0<b)
    (hA : ∀ v,b*‖v‖≤‖A v‖) (hK : A.normDet≤K) (v : E) :
    ‖A v‖≤((finrank ℝ E:ℝ)*K/b^(finrank ℝ E-1))*‖v‖ := by
  classical
  let e := A.isSymmetric_adjoint_comp_self.eigenvectorBasis (rfl : finrank ℝ E=finrank ℝ E)
  have hσ := singularValue_le_of_conorm_det A hb hA hK
  have hK0 : 0≤K := A.normDet_nonneg.trans hK
  have hC : 0≤K/b^(finrank ℝ E-1) := div_nonneg hK0 (pow_pos hb _).le
  calc
    ‖A v‖ = ‖∑ j : Fin (finrank ℝ E), e.repr v j • A (e j)‖ := by
      simp_rw [←map_smul]
      rw [←map_sum,e.sum_repr]
    _ ≤ ∑ j : Fin (finrank ℝ E),‖e.repr v j • A (e j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin (finrank ℝ E),(K/b^(finrank ℝ E-1))*‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul,norm_eigenvector_image_eq_singularValue]
      have he : ‖e.repr v j‖≤‖v‖ := by
        rw [e.repr_apply_apply]
        simpa only [e.norm_eq_one,mul_one,one_mul] using (norm_inner_le_norm (e j) v)
      calc
        ‖e.repr v j‖*A.singularValues j ≤ ‖v‖*(K/b^(finrank ℝ E-1)) :=
          mul_le_mul he (hσ j) (A.singularValues_nonneg j) (norm_nonneg v)
        _ = _ := mul_comm _ _
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] <;> ring

end NormDetCoercivity
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section CoerciveBilinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma bilinearOperator_conorm {W : E →L[ℝ] E →L[ℝ] ℝ} {m : ℝ}
    (hW : ∀ d:E,m*‖d‖^2≤W d d) (d : E) : m*‖d‖≤‖bilinearOperator W d‖ := by
  by_cases hd : d=0
  · simp [hd]
  apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hd)).mp
  calc
    (m*‖d‖)*‖d‖=m*‖d‖^2 := by ring
    _ ≤ W d d := hW d
    _ = inner ℝ (bilinearOperator W d) d := (bilinearOperator_inner W d d).symm
    _ ≤ ‖bilinearOperator W d‖*‖d‖ := real_inner_le_norm _ _

lemma bilinear_quadratic_bound_of_det {W : E →L[ℝ] E →L[ℝ] ℝ} {m K : ℝ}
    (hm : 0 < m) (hW : ∀ d:E,m*‖d‖^2≤W d d)
    (hK : |(bilinearOperator W).det|≤K) (d : E) :
    W d d≤((finrank ℝ E:ℝ)*K/m^(finrank ℝ E-1))*‖d‖^2 := by
  have hK' : (bilinearOperator W).toLinearMap.normDet≤K := by
    rwa [LinearMap.normDet_eq_abs_det]
  have H := norm_le_of_conorm_det (bilinearOperator W).toLinearMap hm
    (bilinearOperator_conorm hW) hK' d
  calc
    W d d = inner ℝ (bilinearOperator W d) d := (bilinearOperator_inner W d d).symm
    _ ≤ ‖bilinearOperator W d‖*‖d‖ := real_inner_le_norm _ _
    _ ≤ (((finrank ℝ E:ℝ)*K/m^(finrank ℝ E-1))*‖d‖)*‖d‖ :=
      mul_le_mul_of_nonneg_right H (norm_nonneg d)
    _ = _ := by ring
end CoerciveBilinear

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_RelativeHessianBound
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
section RelativeHessianBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma relative_hessian_operator_factor {a : M} {z : Model n} {φ : Model n → ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hp : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z)) :
    let b := coordinateBackward a (-1,z,fderiv ℝ φ z)
    bilinearOperator (fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a b)) z) =
      (mixedCostOperator a b z (extChartAt 𝓘(ℝ,Model n) b b)).comp
        (fderiv ℝ (chartTestContact a b φ) z) := by
  dsimp only
  rw [chartTestContact_relative_hessian hz hφ hp]
  apply ContinuousLinearMap.ext
  intro d
  apply ext_inner_right ℝ
  intro e
  simp only [ContinuousLinearMap.comp_apply,bilinearOperator_inner,mixedCostOperator,
    neg_apply]

variable [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_strict_relative_hessian_bound (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0<lam) (hcap : 0 ≤ cap) (a : M) (L : Model n →L[ℝ] ℝ)
    (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)))
    {m : ℝ} (hm : 0 < m) :
    let z := extChartAt 𝓘(ℝ,Model n) a a
    let b := coordinateBackward a (-1,z,L)
    ∃ C≥0, ∀ (x0 : M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ φ : Model n → ℝ, ContDiffAt ℝ 2 φ z → fderiv ℝ φ z=L → uv.1 a=φ z →
      (∃ ε>0,∀ᶠ w in 𝓝 z,ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-φ w) →
      (∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a b)) z d d) →
      ∀ d : Model n,fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a b)) z d d≤C*‖d‖^2 := by
  dsimp only
  let z := extChartAt 𝓘(ℝ,Model n) a a
  let b := coordinateBackward a (-1,z,L)
  let B := mixedCostOperator (n := n) a b z (extChartAt 𝓘(ℝ,Model n) b b)
  obtain ⟨K,hK0,hK⟩ := hmtw.exists_strict_test_det_bound hlam hcap a L hp
  let C := (finrank ℝ (Model n):ℝ)*(|B.det| *K)/m^(finrank ℝ (Model n)-1)
  refine ⟨C,by dsimp [C] <;> positivity,?_⟩
  intro x0 uv huv φ hφ hL hval hgap hpos d
  have hdet := hK x0 uv huv φ hφ hL hval hgap ⟨m,hm,hpos⟩
  let W := fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a b)) z
  have hfactor : bilinearOperator W=B.comp (fderiv ℝ (chartTestContact a b φ) z) := by
    have H := relative_hessian_operator_factor
      ((extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)) hφ
      (show chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
        ((extChartAt 𝓘(ℝ,Model n) a).symm z) from by rwa [hL])
    simpa only [hL] using H
  have hWdet : |(bilinearOperator W).det|≤|B.det| *K := by
    rw [hfactor]
    change |(B.toLinearMap.comp (fderiv ℝ (chartTestContact a b φ) z).toLinearMap).det|≤_
    rw [LinearMap.det_comp,abs_mul]
    exact mul_le_mul_of_nonneg_left hdet (abs_nonneg _)
  exact bilinear_quadratic_bound_of_det hm hpos hWdet d

end RelativeHessianBound
end WeakMTWTransport

end

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenteredQuadratic
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
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section CenteredQuadratic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma centered_half_norm_sq_c2 (z : E) :
    ContDiff ℝ 2 (fun w : E => ‖w-z‖^2/2) :=
  (half_norm_sq_contDiff.comp (contDiff_id.sub contDiff_const)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

lemma centered_half_norm_sq_fderiv (z : E) :
    fderiv ℝ (fun w : E => ‖w-z‖^2/2) z=0 := by
  have hq := (half_norm_sq_hasFDerivAt (z-z)).comp (f := fun w:E => w-z) z ((hasFDerivAt_id z).sub_const z)
  simpa only [Function.comp_def,sub_self,map_zero,ContinuousLinearMap.zero_comp] using hq.fderiv

lemma centered_half_norm_sq_second (z d : E) :
    fderiv ℝ (fderiv ℝ (fun w : E => ‖w-z‖^2/2)) z d d=‖d‖^2 := by
  have hc : ContDiffAt ℝ 2 (fun w:E => ‖w‖^2/2) (z-z) :=
    (half_norm_sq_contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have H := second_fderiv_comp_stationary hc (g := fun w:E => w-z)
    (contDiffAt_id.sub contDiffAt_const)
    (by rw [sub_self,half_norm_sq_fderiv,map_zero]) d d
  have hid : fderiv ℝ (fun w:E => w-z) z=ContinuousLinearMap.id ℝ E :=
    ((hasFDerivAt_id z).sub_const z).fderiv
  simpa only [sub_self,hid,ContinuousLinearMap.id_apply,
    half_norm_sq_second_fderiv,real_inner_self_eq_norm_sq] using H
end CenteredQuadratic

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ActualRelativeHessianBound
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
section ActualRelativeHessianBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_relative_hessian_bound (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0<lam) (hcap : 0 ≤ cap) (a : M) (L : Model n →L[ℝ] ℝ)
    (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)))
    {m : ℝ} (hm : 0 < m) :
    let z := extChartAt 𝓘(ℝ,Model n) a a
    let b := coordinateBackward a (-1,z,L)
    ∃ C≥0, ∀ (x0 : M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ φ : Model n → ℝ, ContDiffAt ℝ 2 φ z → fderiv ℝ φ z=L → uv.1 a=φ z →
      (∀ᶠ w in 𝓝 z,φ w≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)) →
      (∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a b)) z d d) →
      ∀ d : Model n,fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a b)) z d d≤C*‖d‖^2 := by
  dsimp only
  let z := extChartAt 𝓘(ℝ,Model n) a a
  let b := coordinateBackward a (-1,z,L)
  obtain ⟨C,hC,H⟩ := hmtw.exists_strict_relative_hessian_bound hlam hcap a L hp
    (show 0 < m/2 by positivity)
  refine ⟨C+m/2,by positivity,?_⟩
  intro x0 uv huv φ hφ hL hval hlo hpos d
  change fderiv ℝ φ z=L at hL
  change uv.1 a=φ z at hval
  let q : Model n → ℝ := fun w => ‖w-z‖^2/2
  let ψ : Model n → ℝ := fun w => φ w-(m/2)*q w
  have hq : ContDiffAt ℝ 2 q z := (centered_half_norm_sq_c2 z).contDiffAt
  have hψ : ContDiffAt ℝ 2 ψ z := hφ.sub (contDiffAt_const.mul hq)
  have hψL : fderiv ℝ ψ z=L := by
    rw [show ψ=(fun w => φ w-(m/2)*q w) from rfl,
      fderiv_fun_sub (hφ.differentiableAt (by norm_num))
        ((hq.differentiableAt (by norm_num)).const_mul _)]
    change fderiv ℝ φ z-fderiv ℝ ((m/2) • q) z=L
    rw [fderiv_const_smul_field,Pi.smul_apply,centered_half_norm_sq_fderiv,smul_zero,sub_zero,hL]
  have hψval : uv.1 a=ψ z := by simpa [ψ,q] using hval
  have hgap : ∃ ε>0,∀ᶠ w in 𝓝 z,
      ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-ψ w := by
    refine ⟨m/4,by positivity,?_⟩
    filter_upwards [hlo] with w hw
    dsimp only [ψ,q]
    rw [dist_eq_norm]
    nlinarith only [hw]
  have hψH (e : Model n) : fderiv ℝ (fderiv ℝ ψ) z e e=
      fderiv ℝ (fderiv ℝ φ) z e e-(m/2)*‖e‖^2 := by
    rw [show ψ=(fun w => φ w-(m/2)*q w) from rfl,
      second_fderiv_sub hφ (contDiffAt_const.mul hq),second_fderiv_const_mul,
      centered_half_norm_sq_second]
  have hpψ : ∀ e : Model n,(m/2)*‖e‖^2≤fderiv ℝ (fderiv ℝ ψ) z e e+
      fderiv ℝ (fderiv ℝ (chartCost a b)) z e e := by
    intro e
    rw [hψH]
    linarith only [hpos e]
  have HD := H x0 uv huv ψ hψ hψL hψval hgap hpψ d
  rw [hψH] at HD
  nlinarith only [HD]

end ActualRelativeHessianBound
end WeakMTWTransport

end

end

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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_NormalRelativeHessianBound
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section NormalRelativeHessianBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_normal_relative_hessian_bound_oai (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) {a : M}
    {p : TangentSpace 𝓘(ℝ,Model n) a} (hp : p∈injectivityDomain a)
    {m : ℝ} (hm : 0 < m) :
    ∃ C≥0, ∀ (x0 : M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ φ : TangentSpace 𝓘(ℝ,Model n) a → ℝ,
      ContDiffAt ℝ 2 φ 0 → fderiv ℝ φ 0=innerSL ℝ p → uv.1 a=φ 0 →
      (∀ᶠ w in 𝓝 0,φ w≤uv.1 (riemannianExp a w)) →
      (∀ d,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue a p d) →
      ∀ d,fderiv ℝ (fderiv ℝ φ) 0 d d+hessianValue a p d≤C*‖d‖^2 := by
  let z := extChartAt 𝓘(ℝ,Model n) a a
  let V := TangentSpace 𝓘(ℝ,Model n) a
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) a) := inferInstanceAs (FiniteDimensional ℝ (Model n))
  let c := normalCost a p
  obtain ⟨L,hLreg,hLb,hLD⟩ := exists_chart_covector_for_log hp
  obtain ⟨e,he,he0,hei,hi⟩ := exists_smooth_chart_fiber_log (a := a)
    (zero_mem_injectivityDomain (n := n) a)
    (by simpa only [riemannianExp_zero] using mem_extChartAt_source (I := 𝓘(ℝ,Model n)) a)
  simp only [riemannianExp_zero] at he he0 hei hi
  change ContDiffAt ℝ ∞ e z at he
  change e z=0 at he0
  change Function.Injective (fderiv ℝ e z) at hi
  have he2 : ContDiffAt ℝ 2 e z := he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨k,hk,Hk⟩ := exists_norm_sq_lower_of_injective (fderiv ℝ e z) hi
  have hsur : Function.Surjective (fderiv ℝ e z) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)).mp hi
  obtain ⟨C,hC,HC⟩ := hmtw.exists_relative_hessian_bound hlam hcap a L hLreg (mul_pos hm hk)
  refine ⟨C/k,div_nonneg hC hk.le,?_⟩
  intro x0 uv huv φ hφ hφD hval hlo hpos d
  let ψ : Model n → ℝ := fun w => φ (e w)
  have hψ : ContDiffAt ℝ 2 ψ z := (he0.symm ▸ hφ).comp z he2
  have hc : ContDiffAt ℝ 2 c 0 :=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hce : chartCost a (riemannianExp a p) =ᶠ[𝓝 z] (fun w => c (e w)) := by
    filter_upwards [hei] with w hw
    simp only [c,normalCost,chartCost,hw]
  have hcc : ContDiffAt ℝ 2 (chartCost a (riemannianExp a p)) z :=
    ((he0.symm ▸ hc).comp z he2).congr_of_eventuallyEq hce
  have hψD : fderiv ℝ ψ z=L := by
    have Hc := hce.fderiv_eq (𝕜 := ℝ)
    rw [hLD.fderiv,fderiv_fun_comp z
      (by simpa only [he0] using hc.differentiableAt (by norm_num))
      (he2.differentiableAt (by norm_num)),he0,(normalCost_hasFDerivAt_zero hp).fderiv] at Hc
    rw [show ψ=(fun w => φ (e w)) from rfl,fderiv_fun_comp z
      (by simpa only [he0] using hφ.differentiableAt (by norm_num))
      (he2.differentiableAt (by norm_num)),he0,hφD]
    apply ContinuousLinearMap.ext
    intro d
    have H := congrArg (fun A : Model n →L[ℝ] ℝ => A d) Hc
    simpa only [neg_apply,ContinuousLinearMap.comp_apply,
      innerSL_apply_apply,inner_neg_left,neg_inj] using H.symm
  have hψval : uv.1 a=ψ z := by simpa only [ψ,he0] using hval
  have hψlo : ∀ᶠ w in 𝓝 z,ψ w≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w) := by
    have H := he.continuousAt.eventually (show ∀ᶠ v in 𝓝 (e z),φ v≤uv.1 (riemannianExp a v) by rwa [he0])
    filter_upwards [H,hei] with w hw hwi
    simpa only [ψ,hwi] using hw
  have Hpull (d : Model n) : fderiv ℝ (fderiv ℝ ψ) z d d+
      fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp a p))) z d d =
      fderiv ℝ (fderiv ℝ φ) 0 (fderiv ℝ e z d) (fderiv ℝ e z d)+
        hessianValue a p (fderiv ℝ e z d) := by
    have hzF : fderiv ℝ (fun v => φ v+c v) 0=0 := by
      rw [fderiv_fun_add (hφ.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)),
        hφD,(normalCost_hasFDerivAt_zero hp).fderiv]
      simp only [map_neg,add_neg_cancel]
    have HF := second_fderiv_comp_stationary (f := fun v => φ v+c v) (g := e)
      (he0.symm ▸ hφ.add hc) he2 (by rwa [he0]) d d
    rw [he0,second_fderiv_add_eq hφ hc] at HF
    rw [hessianValue_eq_normalHessian hp]
    have Heq : (fun w => ψ w+chartCost a (riemannianExp a p) w) =ᶠ[𝓝 z]
        (fun w => φ (e w)+c (e w)) := by
      filter_upwards [hce] with w hw
      rw [hw]
    have HH := congrArg (fun A : Model n →L[ℝ] Model n →L[ℝ] ℝ => A d d) Heq.fderiv.fderiv_eq
    rw [second_fderiv_add_eq hψ hcc] at HH
    exact HH.trans HF
  have hψpos (d : Model n) : (m*k)*‖d‖^2≤fderiv ℝ (fderiv ℝ ψ) z d d+
      fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,L)))) z d d := by
    rw [hLb,Hpull]
    calc
      _ = m*(k*‖d‖^2) := by ring
      _ ≤ m*‖fderiv ℝ e z d‖^2 := mul_le_mul_of_nonneg_left (Hk d) hm.le
      _ ≤ _ := hpos _
  obtain ⟨w,hw⟩ := hsur d
  have HB := HC x0 uv huv ψ hψ hψD hψval hψlo hψpos w
  rw [hLb,Hpull,hw] at HB
  have Hb := Hk w
  rw [hw] at Hb
  calc
    _ ≤ C*‖w‖^2 := HB
    _ ≤ (C/k)*‖d‖^2 := by
      have HH : ‖w‖^2≤‖d‖^2/k := (le_div_iff₀ hk).mpr (by nlinarith only [Hb])
      convert! mul_le_mul_of_nonneg_left HH hC using 1; ring

end NormalRelativeHessianBound
end WeakMTWTransport

end

end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.exists_normal_relative_hessian_bound_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.exists_normal_relative_hessian_bound_oai.{u_1}
