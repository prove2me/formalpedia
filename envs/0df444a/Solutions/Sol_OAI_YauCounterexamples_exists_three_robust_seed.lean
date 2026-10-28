-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_three_robust_seed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:16:58.966847+00:00
-- url     : https://prove2.me/submissions/63128de2-804c-4775-8863-9e254f156319

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_exists_three_profile_seed
import Theorems.Thm_OAI_YauCounterexamples_threeGlobalLog_local

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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma roundChart_zero (p : E) (L : F →ₗᵢ[ℝ] E) : roundChart p L 0 = p := by
  simp [roundChart,stereoInvFunAux]


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
lemma sphere_chart_symm (p : Sphere n) :
    (fun y => ((chartAt (Euclidean n) p).symm y : Euclidean (n+1))) =
      roundChart (p : Euclidean (n+1)) (sphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : Euclidean (n+1)) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,sphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

lemma sphere_chart_center (p : Sphere n) : chartAt (Euclidean n) p p = 0 := by
  have hh : (chartAt (Euclidean n) p).symm 0 = p := by
    apply Subtype.ext
    change (fun y => ((chartAt (Euclidean n) p).symm y : Euclidean (n+1))) 0 = _
    rw [sphere_chart_symm,roundChart_zero]
  have hz : (0 : Euclidean n) ∈ (chartAt (Euclidean n) p).target := by
    change 0 ∈ (stereographic' n (-p)).target
    simp
  exact (congrArg (chartAt (Euclidean n) p) hh).symm.trans ((chartAt (Euclidean n) p).right_inv hz)


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_UnitSphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]

lemma unitSphere_chart_symm (p : Metric.sphere (0 : A) 1) :
    (fun y => ((chartAt (Euclidean n) p).symm y : A)) =
      roundChart (p : A) (unitSphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : A) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,unitSphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

lemma unitSphere_chart_center (p : Metric.sphere (0 : A) 1) : chartAt (Euclidean n) p p = 0 := by
  have hh : (chartAt (Euclidean n) p).symm 0 = p := by
    apply Subtype.ext
    change (fun y => ((chartAt (Euclidean n) p).symm y : A)) 0 = _
    rw [unitSphere_chart_symm,roundChart_zero]
  have hz : (0 : Euclidean n) ∈ (chartAt (Euclidean n) p).target := by
    change 0 ∈ (stereographic' n (-p)).target
    simp
  exact (congrArg (chartAt (Euclidean n) p) hh).symm.trans ((chartAt (Euclidean n) p).right_inv hz)

end


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CoordinateForm
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
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma metricProfileTraceForm_apply (B H : CoordinateForm E) (a v : E) :
    metricProfileTraceForm B H a v v = B v v*H a a+(1+B a a)*H v v := by
  simp only [metricProfileTraceForm,add_apply,smul_apply,smul_eq_mul]
  ring

attribute [local instance] OAI.YauCounterexamples.dualNorm
attribute [local instance] OAI.YauCounterexamples.dualSpace
omit [FiniteDimensional ℝ E] in

theorem quadraticPlaneStrict_eventually {H : CoordinateForm E} {a : E} (ha : a ≠ 0)
    (hs : quadraticPlaneStrict H a) : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), quadraticPlaneStrict p.1 p.2 := by
  obtain ⟨v,hv,hav,hpos⟩ := hs
  let w : CoordinateForm E × E → E := fun p => v - (inner ℝ p.2 v / ‖p.2‖ ^ 2) • p.2
  have han : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have hsnd : Continuous (fun p : CoordinateForm E × E => p.2) := continuous_snd
  have hw : ContinuousAt w (H,a) := by
    exact continuousAt_const.sub (((hsnd.inner continuous_const).continuousAt.div
      (hsnd.norm.pow 2).continuousAt han).smul hsnd.continuousAt)
  have hwa : w (H,a) = v := by simp [w,hav]
  let z : CoordinateForm E × E → E := fun p => ‖w p‖⁻¹ • w p
  have hz : ContinuousAt z (H,a) :=
    (hw.norm.inv₀ (by rw [hwa,hv]; norm_num)).smul hw
  have hza : z (H,a) = v := by simp [z,hwa,hv]
  have hp : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), 0 < p.1 (z p) (z p) := by
    have hc : ContinuousAt (fun p : CoordinateForm E × E => p.1 (z p) (z p)) (H,a) :=
      (continuousAt_fst.clm_apply hz).clm_apply hz
    apply hc.eventually (Ioi_mem_nhds ?_)
    simpa [hza] using hpos
  have hane : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), p.2 ≠ 0 :=
    continuous_snd.continuousAt.eventually_ne ha
  have hwne : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), w p ≠ 0 :=
    hw.eventually_ne (by rw [hwa]; exact norm_ne_zero_iff.mp (by rw [hv]; norm_num))
  filter_upwards [hp,hane,hwne] with p hp hpa hpw
  refine ⟨z p,?_,?_,hp⟩
  · simp [z,norm_smul,norm_ne_zero_iff.mpr hpw]
  · have hpn : ‖p.2‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hpa)
    have hwperp : inner ℝ p.2 (w p) = 0 := by
      simp only [w, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
      ring
    simp [z,inner_smul_right,hwperp]

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

lemma coordinateKoszul_apply (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (v w z : E) :
    coordinateKoszul D v w z = (D v w z+D w v z-D z v w)/2 := by
  change (1/2 : ℝ) * (D v w z+D w v z-D z v w) = _
  ring

lemma metricChristoffel_pairing (g : SmoothMetric E E) (x v w z : E) :
    selfMetricFlat g x (metricChristoffel g x v w) z =
      (fderiv ℝ (selfMetricFlat g) x v w z+fderiv ℝ (selfMetricFlat g) x w v z-
        fderiv ℝ (selfMetricFlat g) x z v w)/2 := by
  have h := (selfMetricFlat_invertible g x).inverse_apply_eq.mp
    (show (selfMetricFlat g x).inverse (coordinateKoszul (fderiv ℝ (selfMetricFlat g) x) v w) =
      metricChristoffel g x v w from rfl)
  exact (congrArg (fun l : E →L[ℝ] ℝ => l z) h.symm).trans (coordinateKoszul_apply _ _ _ _)


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
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma quadraticPlaneStrict_iff_nonzero (T : CoordinateForm E) (q : E) :
    quadraticPlaneStrict T q ↔ ∃ v, v ≠ 0 ∧ inner ℝ q v = 0 ∧ 0 < T v v := by
  constructor
  · rintro ⟨v,hv,hq,hp⟩
    exact ⟨v,norm_ne_zero_iff.mp (by rw [hv]; norm_num),hq,hp⟩
  · rintro ⟨v,hv,hq,hp⟩
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    refine ⟨‖v‖⁻¹ • v,?_,?_,?_⟩
    · simp [norm_smul,ne_of_gt hn]
    · simp [inner_smul_right,hq]
    · simpa only [map_smul,smul_apply,smul_eq_mul] using
        mul_pos (inv_pos.mpr hn) (mul_pos (inv_pos.mpr hn) hp)


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FderivMetricPairing
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
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [FiniteDimensional ℝ E] in
lemma fderiv_metric_pairing (g : SmoothMetric E E) (x v w z : E) :
    fderiv ℝ (fun y => selfMetricFlat g y w z) x v =
      fderiv ℝ (selfMetricFlat g) x v w z := by
  have hd := (contDiff_selfMetricFlat g).differentiable (by simp)
  rw [fderiv_clm_apply ((hd x).clm_apply (differentiableAt_const w))
      (differentiableAt_const z), fderiv_clm_apply (hd x) (differentiableAt_const w)]
  simp

omit [FiniteDimensional ℝ E] in
lemma fderiv_fderiv_apply {F : E → V} (hF : ContDiff ℝ ∞ F) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ F y w) x v = fderiv ℝ (fderiv ℝ F) x v w := by
  rw [fderiv_clm_apply ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const w)]
  simp

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LinearMetricForm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
lemma linearPullbackMetric_flat (g : SmoothMetric E E) (L : F ≃L[ℝ] E) (x v w : F) :
    selfMetricFlat (linearPullbackMetric g L) x v w = selfMetricFlat g (L x) (L v) (L w) := by
  rw [selfMetricFlat_apply]
  rfl
omit [FiniteDimensional ℝ E] in
lemma linearPullbackMetric_first (g : SmoothMetric E E) (L : F ≃L[ℝ] E) (x v w z : F) :
    fderiv ℝ (selfMetricFlat (linearPullbackMetric g L)) x v w z =
      fderiv ℝ (selfMetricFlat g) (L x) (L v) (L w) (L z) := by
  rw [←fderiv_metric_pairing]
  simp_rw [linearPullbackMetric_flat]
  have hd : DifferentiableAt ℝ (fun y => selfMetricFlat g y (L w) (L z)) (L x) :=
    (((contDiff_selfMetricFlat g).clm_apply contDiff_const).clm_apply contDiff_const).differentiable (by simp) _
  change fderiv ℝ ((fun y => selfMetricFlat g y (L w) (L z)) ∘ L) x v = _
  rw [fderiv_comp x hd L.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply]
  exact fderiv_metric_pairing g (L x) (L v) (L w) (L z)
lemma linearPullbackMetric_Christoffel (g : SmoothMetric E E) (L : F ≃L[ℝ] E) (x v w : F) :
    L (metricChristoffel (linearPullbackMetric g L) x v w) =
      metricChristoffel g (L x) (L v) (L w) := by
  apply (selfMetricFlat_invertible g (L x)).injective
  ext z
  obtain ⟨z,rfl⟩ := L.surjective z
  rw [←linearPullbackMetric_flat,metricChristoffel_pairing,metricChristoffel_pairing]
  simp only [linearPullbackMetric_first]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma fderiv_linearEquiv_comp {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (L : F ≃L[ℝ] E) (x v : F) :
    fderiv ℝ (f ∘ L) x v = fderiv ℝ f (L x) (L v) := by
  rw [fderiv_comp x (hf.differentiable (by simp) _) L.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma second_linearEquiv_comp {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (L : F ≃L[ℝ] E) (x v w : F) :
    fderiv ℝ (fderiv ℝ (f ∘ L)) x v w = fderiv ℝ (fderiv ℝ f) (L x) (L v) (L w) := by
  rw [←fderiv_fderiv_apply (hf.comp L.contDiff)]
  simp_rw [fderiv_linearEquiv_comp hf L]
  change fderiv ℝ ((fun y => fderiv ℝ f y (L w)) ∘ L) x v = _
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ f y (L w)) (L x) :=
    (((hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)) _
  rw [fderiv_comp x hd L.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
  exact fderiv_fderiv_apply hf (L x) (L v) (L w)
lemma linearPullbackMetric_hessian (g : SmoothMetric E E) (L : F ≃L[ℝ] E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x v w : F) :
    actualCoordinateHessian (linearPullbackMetric g L) (f ∘ L) x v w =
      actualCoordinateHessian g f (L x) (L v) (L w) := by
  simp only [actualCoordinateHessian,coordinateCovariantSecond,sub_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply]
  rw [second_linearEquiv_comp hf L,fderiv_linearEquiv_comp hf L,linearPullbackMetric_Christoffel]
lemma linearPullbackMetric_gradient (g : SmoothMetric E E) (L : F ≃L[ℝ] E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : F) :
    L (coordinateMetricGradient (linearPullbackMetric g L) (f ∘ L) x) =
      coordinateMetricGradient g f (L x) := by
  apply (selfMetricFlat_invertible g (L x)).injective
  ext z
  obtain ⟨z,rfl⟩ := L.surjective z
  rw [←linearPullbackMetric_flat]
  have h1 := (selfMetricFlat_invertible (linearPullbackMetric g L) x).inverse_apply_eq.mp
    (show (selfMetricFlat (linearPullbackMetric g L) x).inverse (fderiv ℝ (f ∘ L) x) =
      coordinateMetricGradient (linearPullbackMetric g L) (f ∘ L) x from rfl)
  have h2 := (selfMetricFlat_invertible g (L x)).inverse_apply_eq.mp
    (show (selfMetricFlat g (L x)).inverse (fderiv ℝ f (L x)) = coordinateMetricGradient g f (L x) from rfl)
  rw [←h1,←h2]
  exact fderiv_linearEquiv_comp hf L x z
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_FourThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
lemma three_chart_center (p : ThreeManifold) : chartAt ThreeModel p p = 0 := by
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · exact sphere_chart_center p.1
  · exact unitSphere_chart_center (n:=1) p.2
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ThreeCoupledNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
lemma productAxis_coord (i : Fin 3) (x : Euclidean 3) : inner ℝ (productAxis i) x = x i := by
  simp [productAxis,EuclideanSpace.inner_single_left]
lemma productA_re (x : Euclidean 3) : (productA x).re=x 0 := by simp [productA,planarLinear,productAxis_coord]
lemma productA_im (x : Euclidean 3) : (productA x).im=x 1 := by simp [productA,planarLinear,productAxis_coord]
lemma productB_re (x : Euclidean 3) : (productB x).re=x 0 := by simp [productB,planarLinear,productAxis_coord]
lemma productB_im (x : Euclidean 3) : (productB x).im=x 2 := by simp [productB,planarLinear,productAxis_coord]
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ThreeNoncancelNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
lemma productSphere_norm_sq (p : Sphere 2) : (p:Euclidean 3) 0^2+(p:Euclidean 3) 1^2+(p:Euclidean 3) 2^2=1 := by
  have hn : ‖(p:Euclidean 3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.property
  have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (p:Euclidean 3)
  simpa [hn,Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs,add_assoc] using hh.symm
lemma productA_norm_le (p : Sphere 2) : ‖productA p‖≤1 := by
  have hh := productSphere_norm_sq p
  have hn := Complex.normSq_eq_norm_sq (productA p)
  simp only [Complex.normSq_apply,productA_re,productA_im] at hn
  nlinarith [sq_nonneg ((p:Euclidean 3) 2),norm_nonneg (productA p)]
lemma productB_norm_le (p : Sphere 2) : ‖productB p‖≤1 := by
  have hh := productSphere_norm_sq p
  have hn := Complex.normSq_eq_norm_sq (productB p)
  simp only [Complex.normSq_apply,productB_re,productB_im] at hn
  nlinarith [sq_nonneg ((p:Euclidean 3) 1),norm_nonneg (productB p)]

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PrepDualNorm
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
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
namespace YauCounterexamples
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma coordinateMetricGradient_ne_zero_dual (g : SmoothMetric E E) (u : E → ℝ) (x : E)
    (ha : coordinateMetricGradient g u x ≠ 0) :
    (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0 := by
  intro h
  have hd : fderiv ℝ u x = 0 := (InnerProductSpace.toDual ℝ E).symm.injective
    (by simpa only [map_zero] using h)
  apply ha
  simp only [coordinateMetricGradient,hd,map_zero]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousCompactSmoothJets
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
local instance hmsDerivSpace_rc459b1_1 : NormedSpace ℝ (E →L[ℝ] CoordinateForm E) := inferInstance
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


end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SmDualNorm
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
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma metricJetStrict_actual (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    metricJetStrict g (x,actualCoordinateHessian g u x,fderiv ℝ u x) ↔
      coordinateMetricGradient g u x ≠ 0 ∧ actualProfileStrict g u x := by
  have hn : (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0 ↔
      coordinateMetricGradient g u x ≠ 0 := by
    constructor
    · intro hh h0
      have hd : fderiv ℝ u x = 0 := by
        simpa only [map_zero] using (selfMetricFlat_invertible g x).inverse_apply_eq.mp h0
      exact hh (by simp only [hd,map_zero])
    · exact coordinateMetricGradient_ne_zero_dual g u x
  exact and_congr_left (fun _ => hn)


end

open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
lemma fullStrictJetMap_actual (g : SmoothMetric E E) (f : E → ℝ) (x : E) :
    metricScalarJet g f x ∈ fullStrictJetSet ↔
      coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x := by
  change metricJetStrict g (x,actualCoordinateHessian g f x,fderiv ℝ f x) ↔ _
  exact metricJetStrict_actual g f x
attribute [local instance] OAI.YauCounterexamples.smDualNorm
attribute [local instance] OAI.YauCounterexamples.smDualSpace
attribute [local instance] OAI.YauCounterexamples.smDerivNorm
attribute [local instance] OAI.YauCounterexamples.smFormNorm
attribute [local instance] OAI.YauCounterexamples.smFormSpace
local instance smDerivSpace_rc459b1_1 : NormedSpace ℝ (E →L[ℝ] CoordinateForm E) := inferInstance
lemma continuousAt_fullStrictJetMap {z : HessianJetData E} (hz : z.1.1.IsInvertible) :
    ContinuousAt fullStrictJetMap z := by
  have hi : ContinuousAt (fun w : HessianJetData E => w.1.1.inverse) z :=
    (hz.contDiffAt_map_inverse (n:=∞)).continuousAt.comp
      (f:=fun w : HessianJetData E => w.1.1) (x:=z) continuous_fst.fst.continuousAt
  have ha : ContinuousAt (fun z : HessianJetData E => z.1.1.inverse z.2.1) z :=
    hi.clm_apply continuous_snd.fst.continuousAt
  have hh := continuousAt_metricHessianFromFullJet hz
  have ht : ContinuousAt (fun z : HessianJetData E =>
      metricProfileTraceForm z.1.1 (metricHessianFromFullJet z) (z.1.1.inverse z.2.1)) z := by
    have hB : ContinuousAt (fun w : HessianJetData E => w.1.1) z :=
      continuous_fst.fst.continuousAt
    unfold metricProfileTraceForm
    exact (((hh.clm_apply ha).clm_apply ha).smul hB).add
      ((continuousAt_const.add ((hB.clm_apply ha).clm_apply ha)).smul hh)
  exact ht.prodMk ((InnerProductSpace.toDual ℝ E).symm.continuous.continuousAt.comp
    continuous_snd.fst.continuousAt)
lemma metricScalarJet_strict_interior (g : SmoothMetric E E) (f : E → ℝ) (x : E)
    (h : coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x) :
    metricScalarJet g f x ∈ interior (fullStrictJetSet (E:=E)) := by
  apply mem_interior_iff_mem_nhds.mpr
  have ho : IsOpen {p : CoordinateForm E × E | p.2 ≠ 0 ∧ quadraticPlaneStrict p.1 p.2} := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    exact (continuous_snd.continuousAt.eventually_ne hp.1).and
      (quadraticPlaneStrict_eventually hp.1 hp.2)
  exact (continuousAt_fullStrictJetMap (selfMetricFlat_invertible g x))
    (ho.mem_nhds ((fullStrictJetMap_actual g f x).mpr h))

theorem compact_actual_strict_metric_stability (g₀ : SmoothMetric E E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {K : Set E} (hK : IsCompact K)
    (hs : ∀ x ∈ K, coordinateMetricGradient g₀ f x ≠ 0 ∧ actualProfileStrict g₀ f x) :
    ∃ δ>0, ∀ g : SmoothMetric E E,
      (∀ x ∈ K, ‖selfMetricFlat g x-selfMetricFlat g₀ x‖<δ ∧
        ‖fderiv ℝ (selfMetricFlat g) x-fderiv ℝ (selfMetricFlat g₀) x‖<δ) →
      ∀ x ∈ K, coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x := by
  obtain ⟨δ,hδ,hstable⟩ := compact_map_uniform_interior hK
    (continuous_metricScalarJet g₀ hf)
    (fun x hx => metricScalarJet_strict_interior g₀ f x (hs x hx))
  refine ⟨δ,hδ,?_⟩
  intro g hg x hx
  exact (fullStrictJetMap_actual g f x).mp (hstable x hx (metricScalarJet g f x)
    (dist_metricScalarJet_lt g g₀ f x hδ (hg x hx).1 (hg x hx).2))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeRadiusNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
attribute [local instance] OAI.YauCounterexamples.threeChartNormedSpace
local instance threeChartContinuousSMul_rc459b1_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeChartMetric_selfFlat (g : SmoothMetric ThreeModel ThreeManifold) (p : ThreeManifold) (y : ThreeModel) :
    selfMetricFlat (threeChartMetric g p) y = chartMetricForm g p y := by
  ext v w
  rw [selfMetricFlat_apply]
  rfl
end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeProfilePoint_zero : (threeProfilePoint:Euclidean 3) 0 = 3/5 := rfl
lemma threeProfilePoint_one : (threeProfilePoint:Euclidean 3) 1 = 0 := rfl
lemma threeEnvelopeExponent_pos : 0<threeEnvelopeExponent := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
section LinearStrictTransport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
lemma linearPullbackMetric_trace (g : SmoothMetric E E) (L : F ≃L[ℝ] E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x v : F) :
    actualProfileTraceForm (linearPullbackMetric g L) (f ∘ L) x v v =
      actualProfileTraceForm g f (L x) (L v) (L v) := by
  simp only [actualProfileTraceForm,metricProfileTraceForm_apply]
  rw [linearPullbackMetric_flat,linearPullbackMetric_hessian g L hf,
    linearPullbackMetric_flat,linearPullbackMetric_hessian g L hf,
    linearPullbackMetric_gradient g L hf]
lemma linearPullbackMetric_strict (g : SmoothMetric E E) (L : F ≃L[ℝ] E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : F)
    (h : coordinateMetricGradient g f (L x) ≠ 0 ∧ actualProfileStrict g f (L x)) :
    coordinateMetricGradient (linearPullbackMetric g L) (f ∘ L) x ≠ 0 ∧
      actualProfileStrict (linearPullbackMetric g L) (f ∘ L) x := by
  constructor
  · intro hz
    have hh := linearPullbackMetric_gradient g L hf x
    rw [hz,map_zero] at hh
    exact h.1 hh.symm
  · have hh := h.2
    rw [actualProfileStrict,quadraticPlaneStrict_iff_nonzero] at hh
    rcases hh with ⟨v,hv,hd,ht⟩
    rw [actualProfileStrict,quadraticPlaneStrict_iff_nonzero]
    refine ⟨L.symm v,by simpa using L.symm.injective.ne hv,?_,?_⟩
    · rw [InnerProductSpace.toDual_symm_apply,fderiv_linearEquiv_comp hf L,L.apply_symm_apply]
      simpa only [InnerProductSpace.toDual_symm_apply] using hd
    · rw [linearPullbackMetric_trace g L hf,L.apply_symm_apply]
      exact ht
end LinearStrictTransport
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeGlobalRadius_lower (p : ThreeManifold) : (1/200:ℝ) ≤ threeGlobalRadius p := by
  have ha := Complex.normSq_eq_norm_sq (productA p.1)
  have hb := Complex.normSq_eq_norm_sq (productB p.1)
  simp only [Complex.normSq_apply,productA_re,productA_im,productB_re,productB_im] at ha hb
  have hs := productSphere_norm_sq p.1
  by_contra hn
  have hn : threeGlobalRadius p < 1/200 := lt_of_not_ge hn
  have hA := (le_max_left ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)).trans_lt hn
  have hB := (le_max_right ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)).trans_lt hn
  dsimp [threeCouplingRadius] at hB
  have hB' : ‖productB p.1‖<1/2 := by linarith
  have hA' : ‖productA p.1‖<1/2 := by linarith
  nlinarith [norm_nonneg (productA p.1), norm_nonneg (productB p.1),sq_nonneg ((p.1:Euclidean 3) 0)]
lemma threeGlobalRadius_pos (p : ThreeManifold) : 0<threeGlobalRadius p :=
  lt_of_lt_of_le (by norm_num) (threeGlobalRadius_lower p)
lemma threeGlobalRadius_le_one (p : ThreeManifold) : threeGlobalRadius p≤1 := by
  apply max_le (productA_norm_le p.1)
  have hb:=productB_norm_le p.1
  dsimp [threeCouplingRadius]
  nlinarith [norm_nonneg (productB p.1)]
lemma threeGlobalLog_bounds (p : ThreeManifold) :
    threeEnvelopeExponent*Real.log (1/200) ≤ threeGlobalLog p ∧ threeGlobalLog p≤0 := by
  constructor
  · exact mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) (threeGlobalRadius_lower p))
      threeEnvelopeExponent_pos.le
  · exact mul_nonpos_of_nonneg_of_nonpos threeEnvelopeExponent_pos.le
      (Real.log_nonpos (threeGlobalRadius_pos p).le (threeGlobalRadius_le_one p))
lemma three_chart_symm_zero (p : ThreeManifold) : (chartAt ThreeModel p).symm 0=p := by
  rw [←three_chart_center p]
  exact (chartAt ThreeModel p).left_inv (mem_chart_source _ _)
lemma three_chart_symm_continuous (p : ThreeManifold) : Continuous (chartAt ThreeModel p).symm := by
  exact continuousOn_univ.mp (by simpa only [OpenPartialHomeomorph.symm_source,three_chart_target] using
    (chartAt ThreeModel p).symm.continuousOn)
end


section
open Set Filter Manifold Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise
attribute [local instance] OAI.YauCounterexamples.threeNeighborNormedSpace
local instance threeNeighborContinuousSMul_rc459b1_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma three_metricCoefficients_smooth (g : SmoothMetric (ThreeModel) (ThreeManifold))
    (p : ThreeManifold) : ContDiff ℝ ∞ (metricCoefficients g p) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiffOn_univ.mp (by
    simpa only [three_chart_target] using contDiffOn_metricCoefficient g p i j)

attribute [local instance] OAI.YauCounterexamples.threeNbDualNorm
attribute [local instance] OAI.YauCounterexamples.threeNbDualSpace
attribute [local instance] OAI.YauCounterexamples.threeNbFormNorm
attribute [local instance] OAI.YauCounterexamples.threeNbFormSpace
local instance threeNbDerivNorm_rc459b1_1 : NormedAddCommGroup (ThreeModel →L[ℝ] CoordinateForm ThreeModel) := inferInstance
local instance threeNbDerivSpace_rc459b1_1 : NormedSpace ℝ (ThreeModel →L[ℝ] CoordinateForm ThreeModel) := inferInstance
theorem three_metric_first_jet_neighborhood (g₀ : SmoothMetric (ThreeModel) (ThreeManifold))
    (p : ThreeManifold) {K : Set (ThreeModel)} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    IsSmoothNeighborhood g₀ {g | ∀ x ∈ K,
      ‖selfMetricFlat (threeChartMetric g p) x-selfMetricFlat (threeChartMetric g₀ p) x‖ < δ ∧
      ‖fderiv ℝ (selfMetricFlat (threeChartMetric g p)) x-
        fderiv ℝ (selfMetricFlat (threeChartMetric g₀ p)) x‖ < δ} := by
  let : NormedAddCommGroup
      (Matrix (CoordIndex ThreeModel) (CoordIndex ThreeModel) ℝ →L[ℝ] CoordinateForm ThreeModel) :=
    inferInstanceAs (NormedAddCommGroup
      ((CoordIndex ThreeModel → CoordIndex ThreeModel → ℝ) →L[ℝ]
        (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ)))
  let L := metricMatrixFormCLM (E := ThreeModel)
  let ε := δ/(‖L‖+1)
  have hden : 0 < ‖L‖+1 := by positivity
  have hε : 0 < ε := div_pos hδ hden
  have hmul : ‖L‖*ε < δ := by
    calc
      ‖L‖*ε < (‖L‖+1)*ε := mul_lt_mul_of_pos_right (by linarith) hε
      _ = δ := by dsimp [ε]; field_simp
  let test : Fin 2 × CoordIndex (ThreeModel) × CoordIndex (ThreeModel) →
      CoordinateTest (ThreeModel) (ThreeManifold) := fun q =>
    { center := p, compactSet := K, isCompact := hK,
      inTarget := by rw [three_chart_target]; exact subset_univ K,
      order := q.1.val, row := q.2.1, column := q.2.2 }
  let tests := (Finset.univ : Finset (Fin 2 × CoordIndex (ThreeModel) × CoordIndex (ThreeModel))).toList.map test
  refine ⟨tests,ε,hε,?_⟩
  intro g hg x hx
  have htest (k : Fin 2) (i j : CoordIndex (ThreeModel)) : test (k,i,j) ∈ tests := by
    exact List.mem_map.mpr ⟨(k,i,j),by simp,rfl⟩
  have h₀ (i j : CoordIndex (ThreeModel)) :
      |metricCoefficients g p x i j-metricCoefficients g₀ p x i j| ≤ ε := by
    have hh := hg (test (0,i,j)) (htest 0 i j) x hx
    simpa only [test,Fin.val_zero,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hh.le
  have h₁ (i j : CoordIndex (ThreeModel)) :
      ‖fderiv ℝ (fun y => metricCoefficients g p y i j-metricCoefficients g₀ p y i j) x‖ ≤ ε := by
    have hh := hg (test (1,i,j)) (htest 1 i j) x hx
    simpa only [test,Fin.val_one,norm_iteratedFDeriv_one] using hh.le
  have hb := metricMatrixForm_first_jet_bound
    ((three_metricCoefficients_smooth g p).differentiable (by simp) x)
    ((three_metricCoefficients_smooth g₀ p).differentiable (by simp) x) hε.le h₀ h₁
  have he (g : SmoothMetric (ThreeModel) (ThreeManifold)) :
      selfMetricFlat (threeChartMetric g p) = fun y => metricMatrixForm (metricCoefficients g p y) :=
    by
      ext y v w
      rw [threeChartMetric_selfFlat]
      rfl
  rw [he g,he g₀]
  exact ⟨hb.1.trans_lt hmul,hb.2.trans_lt hmul⟩

end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
lemma threeNormalInv_clean_eventually : ∀ᶠ y : NormalWaveSpace in 𝓝 0,
    1/2≤‖productA (threeNormalInv y).1‖ ∧ ‖productA (threeNormalInv y).1‖≤3/4 := by
  have hA : Continuous (fun y : NormalWaveSpace => ‖productA (threeNormalInv y).1‖) :=
    ((planarLinear _ _).continuous.comp (continuous_subtype_val.comp
      (continuous_fst.comp ((three_chart_symm_continuous _).comp threeNormalEquiv.continuous)))).norm
  have h0 : ‖productA (threeNormalInv 0).1‖=3/5 := by
    have he : productA threeProfileCenter.1=(3/5:ℂ) := by
      apply Complex.ext <;> simp [productA_re,productA_im,threeProfileCenter,threeProfilePoint_zero,threeProfilePoint_one]
    simp only [threeNormalInv,Function.comp_apply,map_zero,three_chart_symm_zero,he]
    norm_num
  filter_upwards [hA.continuousAt.eventually_lt_const (show ‖productA (threeNormalInv 0).1‖<3/4 by rw [h0]; norm_num),
    hA.continuousAt.eventually_const_lt (show (1/2:ℝ)<‖productA (threeNormalInv 0).1‖ by rw [h0]; norm_num)] with y hu hl
  exact ⟨hl.le,hu.le⟩

attribute [local instance] OAI.YauCounterexamples.threeRobustNormedSpace
local instance threeRobustContinuousSMul_rc459b1_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
theorem exists_three_robust_seed_oai :
    ∃ C R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ F : NormalWaveSpace → ℝ,
      ContDiff ℝ ∞ F ∧ (∀ y ∈ closedBall 0 R, F y=threeGlobalLog (threeNormalInv y)) ∧
      (∀ p, C+1≤threeGlobalLog p) ∧
      ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
        IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
        ∀ g ∈ N, ∀ y ∈ closedBall 0 R,
          coordinateMetricGradient (threeNormalMetricOf g) F y ≠ 0 ∧
          actualProfileStrict (threeNormalMetricOf g) F y := by
  obtain ⟨f,hf,hfc,he,r,hr,hs⟩ := exists_three_profile_seed
  obtain ⟨δ,hδ,hstable⟩ := compact_actual_strict_metric_stability
    (threeChartMetric threeBackgroundMetric threeProfileCenter) hf
    (isCompact_closedBall 0 r) hs
  let N : Set (SmoothMetric ThreeModel ThreeManifold) := {g | ∀ x ∈ closedBall 0 r,
    coordinateMetricGradient (threeChartMetric g threeProfileCenter) f x ≠ 0 ∧
    actualProfileStrict (threeChartMetric g threeProfileCenter) f x}
  have hN : IsSmoothNeighborhood threeBackgroundMetric N := by
    obtain ⟨tests,ε,hε,ht⟩ := three_metric_first_jet_neighborhood threeBackgroundMetric
      threeProfileCenter (isCompact_closedBall 0 r) hδ
    exact ⟨tests,ε,hε,fun g hg => hstable (threeChartMetric g threeProfileCenter) (ht g hg)⟩
  let F := f ∘ threeNormalEquiv
  have hF : ContDiff ℝ ∞ F := hf.comp threeNormalEquiv.contDiff
  have ht : Tendsto threeNormalEquiv (𝓝 (0:NormalWaveSpace)) (𝓝 (0:ThreeModel)) :=
    by simpa using (threeNormalEquiv.continuous.continuousAt (x:=0)).tendsto
  have hgerm : F =ᶠ[𝓝 0] threeGlobalLog ∘ threeNormalInv :=
    (he.trans threeGlobalLog_local.symm).comp_tendsto ht
  have hm : ∀ᶠ y : NormalWaveSpace in 𝓝 0, threeNormalEquiv y ∈ ball 0 r :=
    ht (Metric.ball_mem_nhds 0 hr)
  obtain ⟨s,hs0,hss⟩ := Metric.mem_nhds_iff.mp (hgerm.and (hm.and threeNormalInv_clean_eventually))
  let R := s/2
  let C := threeEnvelopeExponent*Real.log (1/200)-1
  refine ⟨C,R,half_pos hs0,?_,F,hF,?_,?_,N,hN,hs,?_⟩
  · intro y hy
    exact (hss (closedBall_subset_ball (half_lt_self hs0) hy)).2.2
  · intro y hy
    exact (hss (closedBall_subset_ball (half_lt_self hs0) hy)).1
  · intro p
    dsimp [C]
    linarith [(threeGlobalLog_bounds p).1]
  · intro g hg y hy
    exact linearPullbackMetric_strict (threeChartMetric g threeProfileCenter)
      threeNormalEquiv hf y (hg _ (ball_subset_closedBall
        (hss (closedBall_subset_ball (half_lt_self hs0) hy)).2.1))

end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_three_robust_seed_oai := @OAI.YauCounterexamples.exists_three_robust_seed_oai
