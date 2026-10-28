-- Prove2me | solution 1 for OAI.YauCounterexamples.sphericalMetricGood_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:45:20.755991+00:00
-- url     : https://prove2.me/submissions/f3e90e22-dd4f-45e7-81ad-099d3959536e

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_sphericalBaseProfile_chart_margins

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_HmoDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma positiveFormOn_iff_unit (P : Submodule ℝ E) (T : CoordinateForm E) :
    positiveFormOn P T ↔ ∀ v ∈ P, ‖v‖ = 1 → 0 < T v v := by
  constructor
  · intro h v hv hn
    exact h v hv (norm_ne_zero_iff.mp (by rw [hn]; norm_num))
  · intro h v hv hv0
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    let w := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by simp [w, norm_smul, hn]
    have hp := h w (P.smul_mem _ hv) hw
    have he : ‖v‖ • w = v := by simp [w, smul_smul, hn]
    have heq : T v v = ‖v‖^2 * T w w := by
      conv_lhs => rw [← he]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact mul_pos (sq_pos_of_ne_zero hn) hp

attribute [local instance] OAI.YauCounterexamples.hmoDualNorm
attribute [local instance] OAI.YauCounterexamples.hmoDualSpace
local instance hmoFormNorm_r69ddca_1 : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance hmoFormSpace_r69ddca_1 : NormedSpace ℝ (CoordinateForm E) := inferInstance
local instance hmoDerivNorm_r69ddca_1 : NormedAddCommGroup (E →L[ℝ] CoordinateForm E) := inferInstance
local instance hmoDerivSpace_r69ddca_1 : NormedSpace ℝ (E →L[ℝ] CoordinateForm E) := inferInstance
theorem isOpen_positiveFormOn (P : Submodule ℝ E) :
    IsOpen {T : CoordinateForm E | positiveFormOn P T} := by
  let S : Set E := {v | v ∈ P ∧ ‖v‖ = 1}
  have hS : IsCompact S := by
    have he : S = (P : Set E) ∩ sphere (0 : E) 1 := by
      ext v
      simp only [S, mem_ofPred_eq, mem_inter_iff, mem_sphere_zero_iff_norm]
      rfl
    rw [he]
    exact (isCompact_sphere 0 1).inter_left P.closed_of_finiteDimensional
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let B : Set (CoordinateForm E × S) := {p | p.1 p.2 p.2 ≤ 0}
  have hT : Continuous (fun p : CoordinateForm E × S => p.1) := continuous_fst
  have hv : Continuous (fun p : CoordinateForm E × S => (p.2 : E)) :=
    continuous_subtype_val.comp continuous_snd
  have hB : IsClosed B := isClosed_le ((hT.clm_apply hv).clm_apply hv) continuous_const
  have hC : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace _ hB
  convert hC.isOpen_compl using 1
  all_goals try with_reducible_and_instances rfl
  ext T
  rw [mem_ofPred_eq, positiveFormOn_iff_unit]
  simp only [mem_compl_iff, mem_image, B, mem_ofPred_eq]
  constructor
  · intro h
    rintro ⟨q,hq,hqT⟩
    subst T
    exact (not_le_of_gt (h q.2 q.2.property.1 q.2.property.2)) hq
  · intro h v hv hn
    by_contra hh
    apply h
    exact ⟨(T,⟨v,hv,hn⟩),not_lt.mp hh,rfl⟩

theorem isOpen_hessianMargins :
    IsOpen {p : CoordinateForm E × CoordinateForm E | hessianMargins p.1 p.2} := by
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨h₁,P,hP,h₂⟩
  have hb : Continuous (fun p : CoordinateForm E × CoordinateForm E => p.1) := continuous_fst
  have hh : Continuous (fun p : CoordinateForm E × CoordinateForm E => p.2) := continuous_snd
  have hc₁ : Continuous (fun p : CoordinateForm E × CoordinateForm E => (1/2 : ℝ) • p.1+p.2) :=
    (hb.const_smul (1/2 : ℝ)).add hh
  have hc₂ : Continuous (fun p : CoordinateForm E × CoordinateForm E => p.2-p.1) :=
    continuous_snd.sub continuous_fst
  have h₁' := ((isOpen_positiveFormOn (⊤ : Submodule ℝ E)).preimage hc₁).mem_nhds h₁
  have h₂' := ((isOpen_positiveFormOn P).preimage hc₂).mem_nhds h₂
  filter_upwards [h₁',h₂'] with q hq₁ hq₂
  exact ⟨hq₁,P,hP,hq₂⟩

omit [FiniteDimensional ℝ E] in
lemma hessianMargins_of_strong (B H : CoordinateForm E)
    (hB : ∀ v, v ≠ 0 → 0 < B v v)
    (h₁ : ∀ v, -(1/4 : ℝ)*B v v ≤ H v v)
    (h₂ : ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, (3/2 : ℝ)*B v v ≤ H v v) : hessianMargins B H := by
  refine ⟨?_,?_⟩
  · intro v _ hv
    change 0 < (1/2 : ℝ)*B v v+H v v
    nlinarith [h₁ v,hB v hv]
  · obtain ⟨P,hP,hp⟩ := h₂
    refine ⟨P,hP,?_⟩
    intro v hv hv0
    change 0 < H v v-B v v
    nlinarith [hp v hv,hB v hv0]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma selfMetricFlat_apply (g : SmoothMetric E E) (x v w : E) :
    selfMetricFlat g x v w = g.inner x v w := rfl

lemma selfMetricFlat_invertible (g : SmoothMetric E E) (x : E) :
    (selfMetricFlat g x).IsInvertible := by
  rw [←localMetricFlat_self g x x]
  exact localMetricFlat_invertible g x x (mem_baseSet_trivializationAt E _ x)


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ActualCoordinateHessianApply
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
section ScalarHessian
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma actualCoordinateHessian_apply (g : SmoothMetric E E) (f : E → ℝ) (x v w : E) :
    actualCoordinateHessian g f x v w =
      fderiv ℝ (fderiv ℝ f) x v w - fderiv ℝ f x (metricChristoffel g x v w) := by
  rfl

lemma actualCoordinateHessian_add (g : SmoothMetric E E) {f h : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (x v w : E) :
    actualCoordinateHessian g (fun y => f y + h y) x v w =
      actualCoordinateHessian g f x v w + actualCoordinateHessian g h x v w := by
  have hfd := hf.differentiable (by simp)
  have hhd := hh.differentiable (by simp)
  simp only [actualCoordinateHessian_apply]
  have he : fderiv ℝ (fun y => f y + h y) =
      fun y => fderiv ℝ f y + fderiv ℝ h y := by
    funext y
    exact fderiv_add (hfd y) (hhd y)
  rw [he, fderiv_fun_add
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    ((hh.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)]
  simp only [add_apply]
  ring

lemma actualCoordinateHessian_const (g : SmoothMetric E E) (c : ℝ) (x v w : E) :
    actualCoordinateHessian g (fun _ => c) x v w = 0 := by
  simp [actualCoordinateHessian_apply, fderiv_const_apply]

end ScalarHessian

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LinearPowerDirectional
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
section StereoJets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma stereoAux_directional (v x w : E) :
    fderiv ℝ (stereoInvFunAux v) x w =
      (‖x‖^2+4)⁻¹ • ((4:ℝ) • w + (2 * inner ℝ x w) • v) -
      ((‖x‖^2+4)⁻¹ ^2 * (2 * inner ℝ x w)) •
        ((4:ℝ) • x + (‖x‖^2-4) • v) := by
  have hn : HasFDerivAt (fun y : E => ‖y‖^2) ((2:ℝ) • innerSL ℝ x) x := by
    simpa only [two_smul] using (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hi := (hasFDerivAt_inv (by positivity : ‖x‖^2+4 ≠ 0)).comp x (hn.add_const 4)
  have hp := ((hasFDerivAt_id x).const_smul (4:ℝ)).add ((hn.sub_const 4).smul_const v)
  have hh := hi.smul hp
  change HasFDerivAt (stereoInvFunAux v) _ x at hh
  rw [hh.fderiv]
  simp only [_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    smul_eq_mul]
  simp [Function.comp_apply,ContinuousLinearMap.comp_apply,smul_add,smul_smul,inv_pow,sub_eq_add_neg]
  module

end StereoJets
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma roundChart_smooth (p : E) (L : F →ₗᵢ[ℝ] E) : ContDiff ℝ ∞ (roundChart p L) :=
  contDiff_stereoInvFunAux.comp L.contDiff

lemma roundChart_directional (p : E) (L : F →ₗᵢ[ℝ] E) (x w : F) :
    fderiv ℝ (roundChart p L) x w = fderiv ℝ (stereoInvFunAux (-p)) (L x) (L w) := by
  rw [show roundChart p L = stereoInvFunAux (-p) ∘ L.toContinuousLinearMap from rfl,
    fderiv_comp x ((contDiff_stereoInvFunAux (m := ∞)).differentiable (by simp)).differentiableAt
      L.toContinuousLinearMap.differentiableAt]
  rw [ContinuousLinearMap.fderiv]
  rfl


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped ContDiff InnerProductSpace Topology




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace

variable {n : ℕ}

attribute [local instance] OAI.YauCounterexamples.instFactEqNatFinrankRealEuclideanHAddOfNat
lemma sphereFrame_orthogonal (p : Sphere n) (w : Euclidean n) :
    inner ℝ (p : Euclidean (n+1)) (sphereFrame p w) = 0 := by
  have hh := ((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm w).property
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hh
  change inner ℝ (p : Euclidean (n+1)) _ = 0
  rw [real_inner_comm]
  change inner ℝ _ (-(p : Euclidean (n+1))) = 0 at hh
  rw [inner_neg_right,neg_eq_zero] at hh
  exact hh

lemma sphere_chart_symm (p : Sphere n) :
    (fun y => ((chartAt (Euclidean n) p).symm y : Euclidean (n+1))) =
      roundChart (p : Euclidean (n+1)) (sphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : Euclidean (n+1)) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,sphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

lemma sphere_coordinate_embedding (p : Sphere n) (y : Euclidean n) (v : Euclidean n) :
    mfderiv 𝓘(ℝ,Euclidean n) 𝓘(ℝ,Euclidean (n+1))
      (fun q : Sphere n => (q : Euclidean (n+1))) ((chartAt (Euclidean n) p).symm y)
      (mfderiv 𝓘(ℝ,Euclidean n) 𝓘(ℝ,Euclidean n) (chartAt (Euclidean n) p).symm y v) =
        fderiv ℝ (roundChart (p : Euclidean (n+1)) (sphereFrame p)) y v := by
  have hy : y ∈ (chartAt (Euclidean n) p).target := by rw [sphere_chart_target]; trivial
  have hh := mfderiv_comp y
    ((contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp)).mdifferentiableAt
    ((contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (n := ∞) p) hy).mdifferentiableAt (by simp))
  have he := congrArg (fun L => L v) hh
  rw [mfderiv_eq_fderiv] at he
  rw [← sphere_chart_symm]
  exact he.symm


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold BoxIntegral Metric
open scoped Topology ContDiff InnerProductSpace

lemma sphericalRadius_nonneg (a b : Euclidean 4) (q : Sphere 3) :
    0 ≤ sphericalRadius a b q := Real.sqrt_nonneg _

lemma sphericalRadius_sq (a b : Euclidean 4) (q : Sphere 3) :
    (sphericalRadius a b q)^2 =
      (inner ℝ a (q : Euclidean 4))^2+(inner ℝ b (q : Euclidean 4))^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma source_axes_orthonormal : inner ℝ sourceAxisOne sourceAxisOne = 1 ∧
    inner ℝ sourceAxisTwo sourceAxisTwo = 1 ∧ inner ℝ sourceAxisOne sourceAxisTwo = 0 := by
  norm_num [sourceAxisOne,sourceAxisTwo,EuclideanSpace.inner_single_left,PiLp.single_apply]


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Module Manifold
open scoped Topology ContDiff InnerProductSpace Matrix



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SphericalBaseProfileRadius
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
variable {n : ℕ}

lemma sphereChartMetric_pairing (g : SmoothMetric (Euclidean n) (Sphere n))
    (p : Sphere n) (y v w : Euclidean n) :
    (sphereChartMetric g p).inner y v w = chartMetricForm g p y v w := rfl

lemma sphereChartMetric_selfFlat (g : SmoothMetric (Euclidean n) (Sphere n))
    (p : Sphere n) (y : Euclidean n) :
    selfMetricFlat (sphereChartMetric g p) y = chartMetricForm g p y := by
  ext v w
  rw [selfMetricFlat_apply, sphereChartMetric_pairing]

lemma sphereChartMetric_round (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg : IsRound g) (p : Sphere 3) (y v w : Euclidean 3) :
    (sphereChartMetric g p).inner y v w =
      inner ℝ (fderiv ℝ (roundChart (p : Euclidean 4) (sphereFrame p)) y v)
        (fderiv ℝ (roundChart (p : Euclidean 4) (sphereFrame p)) y w) := by
  rw [sphereChartMetric_pairing, chartMetricForm_pairing, hg]
  rw [sphere_coordinate_embedding, sphere_coordinate_embedding]
  rfl

lemma sphericalBaseProfile_chart_eq (p : Sphere 3) (a b : Euclidean 4) (t : ℝ) :
    sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm =
      fun z => (Real.log t-t^2) +
        (inner ℝ a (roundChart (p : Euclidean 4) (sphereFrame p) z))^2 +
        (inner ℝ b (roundChart (p : Euclidean 4) (sphereFrame p) z))^2 := by
  funext z
  dsimp [Function.comp_def, sphericalBaseProfile]
  rw [congrFun (sphere_chart_symm p) z]
  ring

lemma sphericalBaseProfile_chart_smooth (p : Sphere 3) (a b : Euclidean 4) (t : ℝ) :
    ContDiff ℝ ∞ (sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm) := by
  rw [sphericalBaseProfile_chart_eq]
  exact (contDiff_const.add (((innerSL ℝ a).contDiff.comp (roundChart_smooth _ _)).pow 2)).add
    (((innerSL ℝ b).contDiff.comp (roundChart_smooth _ _)).pow 2)


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter Manifold BoxIntegral
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousCompactSmoothJets
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.mcfDualNorm
attribute [local instance] OAI.YauCounterexamples.mcfDualSpace
attribute [local instance] OAI.YauCounterexamples.mcfMatrixMapNorm
attribute [local instance] OAI.YauCounterexamples.mcfMapMatrixNorm
omit [FiniteDimensional ℝ E] in
lemma matrix_fderiv_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : E → Matrix ι κ ℝ} {x : E} (hA : DifferentiableAt ℝ A x) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ i j, ‖fderiv ℝ (fun y => A y i j) x‖ ≤ ε) :
    ‖fderiv ℝ A x‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hε (norm_nonneg v))).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hε (norm_nonneg v))).mpr
  intro j
  have he : fderiv ℝ (fun y => A y i j) x v = (fderiv ℝ A x v) i j := by
    rw [fderiv_apply (differentiableAt_pi.mp hA i) j, fderiv_apply hA i]
    rfl
  erw [← he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hb i j) (norm_nonneg v))

attribute [local instance] OAI.YauCounterexamples.mcfFormNorm
attribute [local instance] OAI.YauCounterexamples.mcfFormSpace
theorem metricMatrixForm_first_jet_bound
    {A B : E → Matrix (CoordIndex E) (CoordIndex E) ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h₀ : ∀ i j, |A x i j-B x i j| ≤ ε)
    (h₁ : ∀ i j, ‖fderiv ℝ (fun y => A y i j-B y i j) x‖ ≤ ε) :
    ‖metricMatrixForm (A x)-metricMatrixForm (B x)‖ ≤ ‖metricMatrixFormCLM (E := E)‖*ε ∧
    ‖fderiv ℝ (fun y => metricMatrixForm (A y)) x-
      fderiv ℝ (fun y => metricMatrixForm (B y)) x‖ ≤ ‖metricMatrixFormCLM (E := E)‖*ε := by
  let L := metricMatrixFormCLM (E := E)
  have hF : DifferentiableAt ℝ (fun y => A y-B y) x := hA.sub hB
  have hn : ‖A x-B x‖ ≤ ε := by
    apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro j
    exact h₀ i j
  have hDn : ‖fderiv ℝ (fun y => A y-B y) x‖ ≤ ε := matrix_fderiv_norm_le hF hε h₁
  constructor
  · change ‖L (A x)-L (B x)‖ ≤ ‖L‖*ε
    rw [← map_sub]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg L))
  · have hLA : DifferentiableAt ℝ (fun y => metricMatrixForm (A y)) x := L.differentiableAt.comp x hA
    have hLB : DifferentiableAt ℝ (fun y => metricMatrixForm (B y)) x := L.differentiableAt.comp x hB
    rw [← fderiv_fun_sub hLA hLB]
    have he : (fun y => metricMatrixForm (A y)-metricMatrixForm (B y)) = fun y => L (A y-B y) := by
      funext y
      exact (map_sub L _ _).symm
    rw [he]
    have hd : fderiv ℝ (fun y => L (A y-B y)) x = L.comp (fderiv ℝ (fun y => A y-B y) x) :=
      (L.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
    rw [hd]
    exact (L.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left hDn (norm_nonneg L))


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.hmsDualNorm
attribute [local instance] OAI.YauCounterexamples.hmsDualSpace
attribute [local instance] OAI.YauCounterexamples.hmsFormNorm
attribute [local instance] OAI.YauCounterexamples.hmsFormSpace
attribute [local instance] OAI.YauCounterexamples.hmsDerivNorm
local instance hmsDerivSpace_r69ddca_1 : NormedSpace ℝ (E →L[ℝ] CoordinateForm E) := inferInstance
lemma continuous_coordinateKoszul : Continuous
    (coordinateKoszul : (E →L[ℝ] CoordinateForm E) → E →L[ℝ] CoordinateForm E) := by
  have hDf : Continuous (fun D : E →L[ℝ] CoordinateForm E => D.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.continuous
  exact ((continuous_id.add hDf).sub (continuous_const.clm_comp hDf)).const_smul (1/2 : ℝ)

lemma continuousAt_metricHessianFromFullJet {z : HessianJetData E} (hB : z.1.1.IsInvertible) :
    ContinuousAt (metricHessianFromFullJet : HessianJetData E → CoordinateForm E) z := by
  have hp : ContinuousAt (fun w : HessianJetData E => w.1.1) z :=
    continuous_fst.fst.continuousAt
  have hi : ContinuousAt (fun w : HessianJetData E => w.1.1.inverse) z :=
    (hB.contDiffAt_map_inverse (n := ∞)).continuousAt.comp (f := fun w : HessianJetData E => w.1.1) (x := z) hp
  have hK : Continuous (fun z : HessianJetData E => coordinateKoszul z.1.2) :=
    continuous_coordinateKoszul.comp continuous_fst.snd
  have hΓ : ContinuousAt (fun z : HessianJetData E => christoffelFromJet z.1.1 z.1.2) z :=
    (continuousAt_const.clm_apply hi).clm_comp hK.continuousAt
  exact continuous_snd.snd.continuousAt.sub
    ((continuousAt_const.clm_apply continuous_snd.fst.continuousAt).clm_comp hΓ)

omit [FiniteDimensional ℝ E] in
lemma continuous_metricScalarJet (g : SmoothMetric E E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (metricScalarJet g f) := by
  exact ((contDiff_selfMetricFlat g).continuous.prodMk
      ((contDiff_selfMetricFlat g).continuous_fderiv (by simp))).prodMk
    ((hf.continuous_fderiv (by simp)).prodMk
      ((hf.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)))

lemma metricScalarJet_margin_interior (g : SmoothMetric E E) (f : E → ℝ) (x : E)
    (h : hessianMargins (selfMetricFlat g x) (actualCoordinateHessian g f x)) :
    metricScalarJet g f x ∈ interior (hessianJetMarginSet (E := E)) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hc : ContinuousAt (fun z : HessianJetData E => (z.1.1,metricHessianFromFullJet z))
      (metricScalarJet g f x) :=
    continuous_fst.fst.continuousAt.prodMk
      (continuousAt_metricHessianFromFullJet (selfMetricFlat_invertible g x))
  exact hc ((isOpen_hessianMargins (E := E)).mem_nhds h)

omit [FiniteDimensional ℝ E] in
lemma dist_metricScalarJet_lt (g g₀ : SmoothMetric E E) (f : E → ℝ) (x : E)
    {δ : ℝ} (hδ : 0 < δ)
    (h₀ : ‖selfMetricFlat g x-selfMetricFlat g₀ x‖ < δ)
    (h₁ : ‖fderiv ℝ (selfMetricFlat g) x-fderiv ℝ (selfMetricFlat g₀) x‖ < δ) :
    dist (metricScalarJet g f x) (metricScalarJet g₀ f x) < δ := by
  change max (max (dist (selfMetricFlat g x) (selfMetricFlat g₀ x))
    (dist (fderiv ℝ (selfMetricFlat g) x) (fderiv ℝ (selfMetricFlat g₀) x)))
    (dist (fderiv ℝ f x,fderiv ℝ (fderiv ℝ f) x)
      (fderiv ℝ f x,fderiv ℝ (fderiv ℝ f) x)) < δ
  rw [dist_self, dist_eq_norm, dist_eq_norm]
  exact max_lt (max_lt h₀ h₁) hδ

lemma compact_map_uniform_interior {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    {K : Set X} (hK : IsCompact K) {F : X → Y} (hF : Continuous F) {U : Set Y}
    (hU : ∀ x ∈ K, F x ∈ interior U) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y, dist y (F x) < δ → y ∈ U := by
  have hi : F '' K ⊆ interior U := by
    rintro _ ⟨x,hx,rfl⟩
    exact hU x hx
  obtain ⟨δ,hδ,hδU⟩ := (hK.image hF).exists_thickening_subset_open isOpen_interior hi
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy
  exact interior_subset (hδU (mem_thickening_iff.mpr ⟨F x,⟨x,hx,rfl⟩,hy⟩))

theorem compact_hessianMargins_stability (g₀ : SmoothMetric E E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {K : Set E} (hK : IsCompact K)
    (hmargin : ∀ x ∈ K, hessianMargins (selfMetricFlat g₀ x) (actualCoordinateHessian g₀ f x)) :
    ∃ δ > 0, ∀ g : SmoothMetric E E,
      (∀ x ∈ K, ‖selfMetricFlat g x-selfMetricFlat g₀ x‖ < δ ∧
        ‖fderiv ℝ (selfMetricFlat g) x-fderiv ℝ (selfMetricFlat g₀) x‖ < δ) →
      ∀ x ∈ K, hessianMargins (selfMetricFlat g x) (actualCoordinateHessian g f x) := by
  obtain ⟨δ,hδ,hstable⟩ := compact_map_uniform_interior hK
    (continuous_metricScalarJet g₀ hf)
    (fun x hx => metricScalarJet_margin_interior g₀ f x (hmargin x hx))
  refine ⟨δ,hδ,?_⟩
  intro g hg x hx
  exact hstable x hx (metricScalarJet g f x)
    (dist_metricScalarJet_lt g g₀ f x hδ (hg x hx).1 (hg x hx).2)


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {n : ℕ}

attribute [local instance] OAI.YauCounterexamples.spnENorm
attribute [local instance] OAI.YauCounterexamples.spnESpace
lemma sphere_metricCoefficients_smooth (g : SmoothMetric (Euclidean n) (Sphere n))
    (p : Sphere n) : ContDiff ℝ ∞ (metricCoefficients g p) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiffOn_univ.mp (by
    simpa only [sphere_chart_target] using contDiffOn_metricCoefficient g p i j)

attribute [local instance] OAI.YauCounterexamples.spnDualNorm
attribute [local instance] OAI.YauCounterexamples.spnDualSpace
attribute [local instance] OAI.YauCounterexamples.spnFormNorm
attribute [local instance] OAI.YauCounterexamples.spnFormSpace
local instance spnDerivNorm_r69ddca_1 : NormedAddCommGroup (Euclidean n →L[ℝ] CoordinateForm (Euclidean n)) := inferInstance
local instance spnDerivSpace_r69ddca_1 : NormedSpace ℝ (Euclidean n →L[ℝ] CoordinateForm (Euclidean n)) := inferInstance
attribute [local instance] OAI.YauCounterexamples.spnMatrixMapNorm
theorem sphere_metric_first_jet_neighborhood (g₀ : SmoothMetric (Euclidean n) (Sphere n))
    (p : Sphere n) {K : Set (Euclidean n)} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    IsSmoothNeighborhood g₀ {g | ∀ x ∈ K,
      ‖selfMetricFlat (sphereChartMetric g p) x-selfMetricFlat (sphereChartMetric g₀ p) x‖ < δ ∧
      ‖fderiv ℝ (selfMetricFlat (sphereChartMetric g p)) x-
        fderiv ℝ (selfMetricFlat (sphereChartMetric g₀ p)) x‖ < δ} := by
  let L := metricMatrixFormCLM (E := Euclidean n)
  let ε := δ/(‖L‖+1)
  have hden : 0 < ‖L‖+1 := by positivity
  have hε : 0 < ε := div_pos hδ hden
  have hmul : ‖L‖*ε < δ := by
    calc
      ‖L‖*ε < (‖L‖+1)*ε := mul_lt_mul_of_pos_right (by linarith) hε
      _ = δ := by dsimp [ε]; field_simp
  let test : Fin 2 × CoordIndex (Euclidean n) × CoordIndex (Euclidean n) →
      CoordinateTest (Euclidean n) (Sphere n) := fun q =>
    { center := p, compactSet := K, isCompact := hK,
      inTarget := by rw [sphere_chart_target]; exact subset_univ K,
      order := q.1.val, row := q.2.1, column := q.2.2 }
  let tests := (Finset.univ : Finset (Fin 2 × CoordIndex (Euclidean n) × CoordIndex (Euclidean n))).toList.map test
  refine ⟨tests,ε,hε,?_⟩
  intro g hg x hx
  have htest (k : Fin 2) (i j : CoordIndex (Euclidean n)) : test (k,i,j) ∈ tests := by
    exact List.mem_map.mpr ⟨(k,i,j),by simp,rfl⟩
  have h₀ (i j : CoordIndex (Euclidean n)) :
      |metricCoefficients g p x i j-metricCoefficients g₀ p x i j| ≤ ε := by
    have hh := hg (test (0,i,j)) (htest 0 i j) x hx
    simpa only [test,Fin.val_zero,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hh.le
  have h₁ (i j : CoordIndex (Euclidean n)) :
      ‖fderiv ℝ (fun y => metricCoefficients g p y i j-metricCoefficients g₀ p y i j) x‖ ≤ ε := by
    have hh := hg (test (1,i,j)) (htest 1 i j) x hx
    simpa only [test,Fin.val_one,norm_iteratedFDeriv_one] using hh.le
  have hb := metricMatrixForm_first_jet_bound
    ((sphere_metricCoefficients_smooth g p).differentiable (by simp) x)
    ((sphere_metricCoefficients_smooth g₀ p).differentiable (by simp) x) hε.le h₀ h₁
  have he (g : SmoothMetric (Euclidean n) (Sphere n)) :
      selfMetricFlat (sphereChartMetric g p) = fun y => metricMatrixForm (metricCoefficients g p y) :=
    funext (sphereChartMetric_selfFlat g p)
  rw [he g,he g₀]
  exact ⟨hb.1.trans_lt hmul,hb.2.trans_lt hmul⟩

theorem sphericalBaseProfile_neighborhood (g₀ : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg₀ : IsRound g₀) (p : Sphere 3) (a b : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (t : ℝ) {K : Set (Euclidean 3)} (hK : IsCompact K)
    (hr : ∀ y ∈ K, (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) a)^2 +
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) b)^2 ≤ 1/8) :
    IsSmoothNeighborhood g₀ {g | ∀ y ∈ K,
      hessianMargins (selfMetricFlat (sphereChartMetric g p) y)
        (actualCoordinateHessian (sphereChartMetric g p)
          (sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm) y)} := by
  have hm (y : Euclidean 3) (hy : y ∈ K) :
      hessianMargins (selfMetricFlat (sphereChartMetric g₀ p) y)
        (actualCoordinateHessian (sphereChartMetric g₀ p)
          (sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm) y) := by
    have hh := sphericalBaseProfile_chart_margins g₀ hg₀ p a b ha hb hab t y (hr y hy)
    exact hessianMargins_of_strong _ _ (fun v hv => by
      rw [selfMetricFlat_apply]; exact (sphereChartMetric g₀ p).pos _ _ hv) hh.1 hh.2
  obtain ⟨δ,hδ,hstable⟩ := compact_hessianMargins_stability (sphereChartMetric g₀ p)
    (sphericalBaseProfile_chart_smooth p a b t) hK hm
  obtain ⟨tests,ε,hε,htests⟩ := sphere_metric_first_jet_neighborhood g₀ p hK hδ
  refine ⟨tests,ε,hε,?_⟩
  intro g hg
  exact hstable (sphereChartMetric g p) (htests g hg)


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Metric
open scoped Topology ContDiff

lemma IsSmoothNeighborhood.mono {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] (g₀ : SmoothMetric E M) {N O : Set (SmoothMetric E M)}
    (hN : IsSmoothNeighborhood g₀ N) (hNO : N ⊆ O) : IsSmoothNeighborhood g₀ O := by
  obtain ⟨tests,ε,hε,h⟩ := hN
  exact ⟨tests,ε,hε,fun g hg => hNO (h g hg)⟩

lemma IsSmoothNeighborhood.inter {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] (g₀ : SmoothMetric E M) {N O : Set (SmoothMetric E M)}
    (hN : IsSmoothNeighborhood g₀ N) (hO : IsSmoothNeighborhood g₀ O) :
    IsSmoothNeighborhood g₀ (N ∩ O) := by
  obtain ⟨t,ε,hε,h⟩ := hN
  obtain ⟨s,δ,hδ,k⟩ := hO
  refine ⟨t++s,min ε δ,lt_min hε hδ,fun g hg => ⟨h g ?_,k g ?_⟩⟩
  · intro a ha y hy
    exact (hg a (List.mem_append_left _ ha) y hy).trans_le (min_le_left _ _)
  · intro a ha y hy
    exact (hg a (List.mem_append_right _ ha) y hy).trans_le (min_le_right _ _)


end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_SphericalBaseProfileChartHessian
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff

lemma sphericalBaseProfile_chart_hessian_param
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (p : Sphere 3)
    (a b : Euclidean 4) (s t : ℝ) (y : Euclidean 3) :
    actualCoordinateHessian (sphereChartMetric g p)
      (sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm) y =
    actualCoordinateHessian (sphereChartMetric g p)
      (sphericalBaseProfile a b s ∘ (chartAt (Euclidean 3) p).symm) y := by
  have he : sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm =
      fun z => (Real.log t-t^2-(Real.log s-s^2)) +
        (sphericalBaseProfile a b s ∘ (chartAt (Euclidean 3) p).symm) z := by
    funext z
    dsimp [sphericalBaseProfile,Function.comp_def]
    ring
  rw [he]
  ext v w
  rw [actualCoordinateHessian_add _ contDiff_const (sphericalBaseProfile_chart_smooth p a b s),
    actualCoordinateHessian_const,zero_add]

lemma sphericalRadius_chart_sq (p : Sphere 3) (a b : Euclidean 4) (y : Euclidean 3) :
    (sphericalRadius a b ((chartAt (Euclidean 3) p).symm y))^2 =
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) a)^2 +
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) b)^2 := by
  rw [sphericalRadius_sq,congrFun (sphere_chart_symm p) y]
  rw [real_inner_comm a,real_inner_comm b]

theorem sphericalBaseProfile_uniform_neighborhood
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀) :
    IsSmoothNeighborhood g₀ {g | ∀ t : ℝ, ∀ y ∈
      sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      hessianMargins (selfMetricFlat (sphereChartMetric g sourcePole) y)
        (actualCoordinateHessian (sphereChartMetric g sourcePole)
          (sphericalBaseProfile sourceAxisOne sourceAxisTwo t ∘
            (chartAt (Euclidean 3) sourcePole).symm) y)} := by
  obtain ⟨ha,hb,hab⟩ := source_axes_orthonormal
  have hK := sphericalCoverage_compact sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole (R := 3/10) (by norm_num)
  have hr : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      (inner ℝ (roundChart (sourcePole : Euclidean 4) (sphereFrame sourcePole) y) sourceAxisOne)^2 +
      (inner ℝ (roundChart (sourcePole : Euclidean 4) (sphereFrame sourcePole) y) sourceAxisTwo)^2
        ≤ 1/8 := by
    intro y hy
    have hb := (mem_sphericalCoverage_iff sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole (R := 3/10) (by norm_num) y).mp hy
    rw [← sphericalRadius_chart_sq]
    have hn := sphericalRadius_nonneg sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y)
    nlinarith
  obtain ⟨tests,ε,hε,htests⟩ := sphericalBaseProfile_neighborhood g₀ hg₀ sourcePole
    sourceAxisOne sourceAxisTwo ha hb hab 0 hK hr
  refine ⟨tests,ε,hε,?_⟩
  intro g hg t y hy
  rw [sphericalBaseProfile_chart_hessian_param g sourcePole sourceAxisOne sourceAxisTwo 0 t]
  exact htests g hg y hy



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SourceSignBox
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter Manifold MeasureTheory BoxIntegral
open scoped Topology ContDiff
namespace YauCounterexamples

lemma sphericalProfileMetricNeighborhood_isNeighborhood
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀) :
    IsSmoothNeighborhood g₀ sphericalProfileMetricNeighborhood :=
  sphericalBaseProfile_uniform_neighborhood g₀ hg₀

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_SourceRoundChartMetricUpper
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter Manifold
open scoped Topology ContDiff InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma roundChart_metric_conformal (p : E) (L : F →ₗᵢ[ℝ] E)
    (hp : inner ℝ p p=1) (hL : ∀ v, inner ℝ p (L v)=0) (x v w : F) :
    inner ℝ (fderiv ℝ (roundChart p L) x v) (fderiv ℝ (roundChart p L) x w) =
      (16/(‖x‖^2+4)^2)*inner ℝ v w := by
  have hL' : ∀ v, inner ℝ (L v) p=0 := fun v => (real_inner_comm _ _).trans (hL v)
  rw [roundChart_directional,roundChart_directional,stereoAux_directional,stereoAux_directional]
  simp only [inner_sub_left,inner_sub_right,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,inner_neg_left,inner_neg_right,
    L.norm_map,L.inner_map_map,hp,hL,hL',real_inner_self_eq_norm_sq,starRingEnd_apply,star_trivial]
  have hpos : ‖x‖^2+4 ≠ 0 := by positivity
  rw [real_inner_comm v x,real_inner_comm w x]
  field_simp
  ring

lemma roundChart_pole_pairing (p : E) (L : F →ₗᵢ[ℝ] E)
    (hp : inner ℝ p p=1) (hL : ∀ v, inner ℝ p (L v)=0) (x : F) :
    1+inner ℝ p (roundChart p L x)=8/(‖x‖^2+4) := by
  simp only [roundChart,stereoInvFunAux,inner_smul_right,inner_add_right,
    inner_neg_right,hp,hL,L.norm_map,mul_zero,zero_add]
  have hpos : ‖x‖^2+4 ≠ 0 := by positivity
  field_simp
  ring


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter Manifold Metric
open scoped Topology ContDiff InnerProductSpace

lemma source_round_chart_metric_upper
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {y : Euclidean 3}
    (hy : y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10))
    (v : Euclidean 3) :
    selfMetricFlat (sphereChartMetric g₀ sourcePole) y v v ≤ (1/2:ℝ)*‖v‖^2 := by
  let q := (chartAt (Euclidean 3) sourcePole).symm y
  have hp : inner ℝ (sourcePole : Euclidean 4) (sourcePole : Euclidean 4)=1 :=
    source_axes_orthonormal.1
  have hr := (mem_sphericalCoverage_iff sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole (by norm_num : (3/10:ℝ)<1) y).mp hy
  have hrs := sphericalRadius_sq sourceAxisOne sourceAxisTwo q
  have hr0 := sphericalRadius_nonneg sourceAxisOne sourceAxisTwo q
  have hx : |inner ℝ sourceAxisOne (q : Euclidean 4)| ≤ 3/10 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤3/10)).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (inner ℝ sourceAxisTwo (q : Euclidean 4))]
  have hh := roundChart_pole_pairing (sourcePole : Euclidean 4)
    (sphereFrame sourcePole) hp (sphereFrame_orthogonal sourcePole) y
  rw [←congrFun (sphere_chart_symm sourcePole) y] at hh
  change 1+inner ℝ sourceAxisOne (q : Euclidean 4)=8/(‖y‖^2+4) at hh
  have hden : ‖y‖^2+4 ≠ 0 := by positivity
  have he : 16/(‖y‖^2+4)^2 = (1+inner ℝ sourceAxisOne (q:Euclidean 4))^2/4 := by
    rw [hh]
    field_simp
    ring
  rw [selfMetricFlat_apply,sphereChartMetric_round g₀ hg₀,
    roundChart_metric_conformal _ _ hp (sphereFrame_orthogonal sourcePole),he,
    real_inner_self_eq_norm_sq]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hx' := abs_le.mp hx
  nlinarith

theorem spherical_coordinate_upper_neighborhood
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀) :
    IsSmoothNeighborhood g₀ {g | ∀ y ∈
      sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2} := by
  have hK := sphericalCoverage_compact sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole (by norm_num : (3/10:ℝ)<1)
  apply IsSmoothNeighborhood.mono g₀ (sphere_metric_first_jet_neighborhood g₀ sourcePole hK
    (by norm_num : (0:ℝ)<1/2))
  intro g hg y hy v
  have hdiff := (hg y hy).1
  have hb := source_round_chart_metric_upper g₀ hg₀ hy v
  have he : |selfMetricFlat (sphereChartMetric g sourcePole) y v v-
      selfMetricFlat (sphereChartMetric g₀ sourcePole) y v v| ≤ (1/2:ℝ)*‖v‖^2 := by
    calc
      _ = ‖(selfMetricFlat (sphereChartMetric g sourcePole) y-
        selfMetricFlat (sphereChartMetric g₀ sourcePole) y) v v‖ := by simp
      _ ≤ ‖selfMetricFlat (sphereChartMetric g sourcePole) y-
        selfMetricFlat (sphereChartMetric g₀ sourcePole) y‖*‖v‖*‖v‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hdiff.le (sq_nonneg ‖v‖)]
  have hh := (abs_le.mp he).2
  linarith



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_SphericalOpenFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions
namespace YauCounterexamples
lemma sphericalMetricGood_neighborhood_oai (g₀ : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg₀ : IsRound g₀) : IsSmoothNeighborhood g₀ {g | SphericalMetricGood g} :=
  IsSmoothNeighborhood.inter g₀ (sphericalProfileMetricNeighborhood_isNeighborhood g₀ hg₀)
    (spherical_coordinate_upper_neighborhood g₀ hg₀)

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.sphericalMetricGood_neighborhood_oai := @OAI.YauCounterexamples.sphericalMetricGood_neighborhood_oai
