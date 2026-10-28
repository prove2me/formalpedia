-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_global_spherical_wave_profile
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:07:50.144352+00:00
-- url     : https://prove2.me/submissions/d36c3b59-3941-4fc7-96b1-0229004c2c4d

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_exists_global_box_amplified_profile

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

end YauCounterexamples

end

end OAI
end

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
lemma hessianMargins_lower {B H : CoordinateForm E} (h : hessianMargins B H) :
    ∀ v, -(1/2 : ℝ)*B v v ≤ H v v := by
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · have hh := h.1 v (by trivial) hv
    change 0 < (1/2 : ℝ)*B v v+H v v at hh
    linarith

omit [FiniteDimensional ℝ E] in
lemma hessianMargins_plane {B H : CoordinateForm E} (h : hessianMargins B H) :
    ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧ ∀ v ∈ P, B v v ≤ H v v := by
  obtain ⟨P,hP,hp⟩ := h.2
  refine ⟨P,hP,?_⟩
  intro v hv
  by_cases hv0 : v = 0
  · simp [hv0]
  · have hh := hp v hv hv0
    change 0 < H v v-B v v at hh
    linarith

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

lemma selfMetricFlat_invertible (g : SmoothMetric E E) (x : E) :
    (selfMetricFlat g x).IsInvertible := by
  rw [←localMetricFlat_self g x x]
  exact localMetricFlat_invertible g x x (mem_baseSet_trivializationAt E _ x)


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
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [FiniteDimensional ℝ E] in
lemma sphere_immersion_normal_first {F : E → V} (hF : ContDiff ℝ ∞ F) {x : E}
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1) (v : E) :
    inner ℝ (F x) (fderiv ℝ F x v) = 0 := by
  have he : (fun y => inner ℝ (F y) (F y)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := hn
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) he.fderiv_eq
  have hd := hF.differentiable (by simp) x
  rw [fderiv_inner_apply ℝ hd hd] at hh
  simp only [fderiv_const_apply, zero_apply,
    real_inner_comm (F x)] at hh
  linarith

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_SphereImmersionSpans
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
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
theorem sphere_immersion_spans (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ v w : E, g.inner x v w =
      inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1) :
    ∀ b : V, ∃ z : E, ∃ t : ℝ, b = fderiv ℝ F x z + t • F x := by
  let A := (fderiv ℝ F x).toLinearMap
  have hinj : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro v hv
    have hz : fderiv ℝ F x v = 0 := hv
    by_contra hnz
    have hp := g.pos x v hnz
    rw [hg, hz, inner_zero_left] at hp
    exact (lt_irrefl 0 hp)
  have hp : F x ≠ 0 := by
    intro hz
    have hh := hn.self_of_nhds
    simp [hz] at hh
  let P : Submodule ℝ V := (ℝ ∙ F x)ᗮ
  have hle : LinearMap.range A ≤ P := by
    rintro _ ⟨v,rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [real_inner_comm]
    exact sphere_immersion_normal_first hF hn v
  have : Fact (Module.finrank ℝ V = Module.finrank ℝ E + 1) := ⟨hd⟩
  have hr : Module.finrank ℝ (LinearMap.range A) = Module.finrank ℝ P := by
    rw [LinearMap.finrank_range_of_inj hinj]
    exact (Submodule.finrank_orthogonal_span_singleton hp).symm
  have he : LinearMap.range A = P := Submodule.eq_of_le_of_finrank_eq hle hr
  intro b
  have hb : b - (inner ℝ (F x) b) • F x ∈ P := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp only [inner_sub_left, real_inner_smul_left, hn.self_of_nhds]
    rw [real_inner_comm b (F x)]
    ring
  rw [← he] at hb
  obtain ⟨z,hz⟩ := hb
  refine ⟨z,inner ℝ (F x) b,?_⟩
  change b = A z + _
  rw [hz]
  module

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_PlanePairMap
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
open Set Filter
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma projectedPlaneMap_tangent (p a b : V) (hp : inner ℝ p p = 1) (c : ℝ × ℝ) :
    inner ℝ p (projectedPlaneMap p a b c) = 0 := by
  simp only [projectedPlaneMap, LinearMap.comp_apply, tangentProjection_apply,
    inner_sub_right, inner_smul_right, hp, mul_one, sub_self]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ActualCoordinateHessianApply
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
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
section ScalarHessian
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [FiniteDimensional ℝ E] in
lemma fderiv_clm_comp_apply (L : V →L[ℝ] ℝ) {F : E → V}
    (hF : ContDiff ℝ ∞ F) (x v : E) :
    fderiv ℝ (fun y => L (F y)) x v = L (fderiv ℝ F x v) := by
  change (fderiv ℝ (L ∘ F) x) v = _
  rw [(L.hasFDerivAt.comp x ((hF.differentiable (by simp) x).hasFDerivAt)).fderiv]
  rfl

end ScalarHessian

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_SphereImmersionTangentSurjective
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
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
lemma sphere_immersion_tangent_surjective (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ v w : E, g.inner x v w = inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1)
    {b : V} (hb : inner ℝ (F x) b = 0) : ∃ z : E, fderiv ℝ F x z = b := by
  obtain ⟨z,t,ht⟩ := sphere_immersion_spans g hF hg hn hd b
  have hzero : t = 0 := by
    have hh := congrArg (inner ℝ (F x)) ht
    rw [hb, inner_add_right, inner_smul_right, hn.self_of_nhds,
      sphere_immersion_normal_first hF hn z] at hh
    linarith
  exact ⟨z,by simpa [hzero] using ht.symm⟩

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ManifoldChartPush
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
open Set Filter Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [NormedSpace ℝ E] [NormedSpace ℝ V] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma manifoldChartPush_apply (p : M) (f : E → V) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    manifoldChartPush p f ((chartAt E p).symm y) = f y := by
  simp only [manifoldChartPush, Set.indicator_of_mem ((chartAt E p).map_target hy),
    Function.comp_apply, (chartAt E p).right_inv hy]

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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma roundChart_smooth (p : E) (L : F →ₗᵢ[ℝ] E) : ContDiff ℝ ∞ (roundChart p L) :=
  contDiff_stereoInvFunAux.comp L.contDiff


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

lemma orthogonal_pair_sq_le (a b q : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    (inner ℝ a q)^2+(inner ℝ b q)^2 ≤ inner ℝ q q := by
  have hba : inner ℝ b a = 0 := (real_inner_comm a b).trans hab
  have hqa : inner ℝ q a = inner ℝ a q := real_inner_comm a q
  have hqb : inner ℝ q b = inner ℝ b q := real_inner_comm b q
  have h := real_inner_self_nonneg (x := q-(inner ℝ a q) • a-(inner ℝ b q) • b)
  simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    ha,hb,hab,hba,hqa,hqb] at h
  nlinarith

lemma sphericalRadius_le_one (a b : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (q : Sphere 3) : sphericalRadius a b q ≤ 1 := by
  have h := orthogonal_pair_sq_le a b q ha hb hab
  have hq : ‖(q : Euclidean 4)‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using q.property
  rw [real_inner_self_eq_norm_sq,hq,one_pow,← sphericalRadius_sq] at h
  nlinarith [sphericalRadius_nonneg a b q]

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
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_RadialBaseEnvelope
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
open Set Filter Manifold
open scoped Topology ContDiff
open Set
namespace YauCounterexamples

lemma log_upper_three_tenths {t : ℝ} (ht : 0 < t) (hT : t ≤ 3/10) :
    Real.log t < -1 := by
  have hq : t < (3/4 : ℝ)^4 := by norm_num at *; linarith
  have hlog := Real.log_lt_log ht hq
  rw [Real.log_pow] at hlog
  have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3/4 by norm_num)
  norm_num at hlog hh
  linarith

lemma radialBaseEnvelope_inside {t r : ℝ} (ht : 0 < t) (hT : t ≤ 3/10)
    (hr : 0 < r) (hrt : r < t) : Real.log r < radialBaseEnvelope t r := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hr ht)
  rw [Real.log_div hr.ne' ht.ne'] at hlog
  have hsq : t*t ≤ (3/10 : ℝ)*(3/10) := mul_self_le_mul_self ht.le hT
  have hmul : t*r ≤ (3/10 : ℝ)*(3/10) :=
    mul_le_mul hT (hrt.le.trans hT) hr.le (by norm_num)
  have hbound : t*(t+r) < 1 := by nlinarith
  have hfac : 0 < (t-r)*(1-t*(t+r)) := mul_pos (sub_pos.mpr hrt) (sub_pos.mpr hbound)
  have hrat : r/t-1 < r^2-t^2 := by
    apply sub_lt_iff_lt_add.mpr
    apply (div_lt_iff₀ ht).mpr
    nlinarith
  dsimp [radialBaseEnvelope]
  linarith

lemma radialBaseEnvelope_outside {t r : ℝ} (ht : 0 < t) (hT : t ≤ 3/10)
    (htr : t < r) (hr : r ≤ 1) : radialBaseEnvelope t r < Real.log r := by
  have ht1 : t < 1 := by linarith
  have hr0 : 0 < r := ht.trans htr
  have htsq : t^2 < 1 := by nlinarith
  have hrsq : r^2 ≤ 1 := by nlinarith
  have htrs : t^2 < r^2 := by nlinarith
  let A := (1-r^2)/(1-t^2)
  let B := (r^2-t^2)/(1-t^2)
  have hden : 0 < 1-t^2 := sub_pos.mpr htsq
  have hA : 0 ≤ A := div_nonneg (by linarith) hden.le
  have hB : 0 < B := div_pos (sub_pos.mpr htrs) hden
  have hsum : A+B=1 := by dsimp [A,B]; field_simp; ring
  have harg : A*t^2+B*1=r^2 := by dsimp [A,B]; field_simp; ring
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2
    (show t^2 ∈ Ioi (0 : ℝ) by exact sq_pos_of_pos ht)
    (show (1 : ℝ) ∈ Ioi (0 : ℝ) by norm_num) hA hB.le hsum
  simp only [smul_eq_mul, harg,Real.log_one,mul_zero,add_zero,Real.log_pow,
    Nat.cast_ofNat] at hlog
  have hbase : Real.log t+1-t^2 < 0 := by
    have hh := log_upper_three_tenths ht hT
    nlinarith [sq_nonneg t]
  have hneg := mul_neg_of_pos_of_neg hB hbase
  have hscale : B*(1-t^2)=r^2-t^2 := by dsimp [B]; field_simp
  dsimp [radialBaseEnvelope]
  nlinarith

theorem radialBaseEnvelope_uniform_sign_margin :
    ∃ η > 0, ∀ t ∈ Icc (1/5 : ℝ) (3/10), ∀ r ∈ Icc (1/20 : ℝ) (1/8),
      η < radialBaseEnvelope t r-Real.log r := by
  let K : Set (ℝ × ℝ) := Icc (1/5 : ℝ) (3/10) ×ˢ Icc (1/20 : ℝ) (1/8)
  let F := fun q : ℝ × ℝ => radialBaseEnvelope q.1 q.2-Real.log q.2
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hne : K.Nonempty := ⟨(1/5,1/20),by norm_num [K]⟩
  have hc : ContinuousOn F K := by
    apply ContinuousOn.sub
    · exact ((Real.continuousOn_log.comp continuousOn_fst
        (fun q hq => (show q.1 ≠ 0 by have := hq.1.1; change q.1 ≠ 0; linarith))).add
        (continuousOn_snd.pow 2)).sub (continuousOn_fst.pow 2)
    · exact Real.continuousOn_log.comp continuousOn_snd
        (fun q hq => (show q.2 ≠ 0 by have := hq.2.1; change q.2 ≠ 0; linarith))
  obtain ⟨q,hq,hmin⟩ := hK.exists_isMinOn hne hc
  have hp : 0 < F q := by
    have hh := radialBaseEnvelope_inside (t := q.1) (r := q.2)
      (by have := hq.1.1; linarith) hq.1.2 (by have := hq.2.1; linarith)
      (by have := hq.1.1; have := hq.2.2; linarith)
    exact sub_pos.mpr hh
  refine ⟨F q/2,by positivity,?_⟩
  intro t ht r hr
  exact (half_lt_self hp).trans_le (hmin (show (t,r) ∈ K from ⟨ht,hr⟩))

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
open Set Filter
open scoped Topology InnerProductSpace
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
lemma quadratic_profile_fderiv {F : E → V} (hF : ContDiff ℝ ∞ F)
    (a b : V) (C : ℝ) (x v : E) :
    fderiv ℝ (fun y => C+(inner ℝ a (F y))^2+(inner ℝ b (F y))^2) x v =
      2*(inner ℝ a (F x)*inner ℝ a (fderiv ℝ F x v)+
        inner ℝ b (F x)*inner ℝ b (fderiv ℝ F x v)) := by
  have ha : ContDiff ℝ ∞ (fun y => inner ℝ a (F y)) := (innerSL ℝ a).contDiff.comp hF
  have hb : ContDiff ℝ ∞ (fun y => inner ℝ b (F y)) := (innerSL ℝ b).contDiff.comp hF
  have hsq {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
      fderiv ℝ (fun y => (f y)^2) x v = 2*f x*fderiv ℝ f x v := by
    simp only [pow_two]
    rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hf.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [fderiv_fun_add ((contDiff_const.add (ha.pow 2)).differentiable (by simp) x)
      ((hb.pow 2).differentiable (by simp) x),
    fderiv_fun_add (differentiableAt_const C) ((ha.pow 2).differentiable (by simp) x)]
  simp only [add_apply, fderiv_const_apply, zero_add]
  have hla := fderiv_clm_comp_apply (innerSL ℝ a) hF x v
  have hlb := fderiv_clm_comp_apply (innerSL ℝ b) hF x v
  simp only [innerSL_apply_apply] at hla hlb
  rw [hsq ha, hsq hb, hla, hlb]
  ring

omit [FiniteDimensional ℝ E] in
theorem sphere_quadratic_profile_fderiv_ne_zero (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ v w : E, g.inner x v w = inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1)
    (a b : V) (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1)
    (hab : inner ℝ a b = 0) (C : ℝ)
    (hr₀ : 0 < (inner ℝ (F x) a)^2+(inner ℝ (F x) b)^2)
    (hr₁ : (inner ℝ (F x) a)^2+(inner ℝ (F x) b)^2 < 1) :
    fderiv ℝ (fun y => C+(inner ℝ a (F y))^2+(inner ℝ b (F y))^2) x ≠ 0 := by
  let A := inner ℝ (F x) a
  let B := inner ℝ (F x) b
  obtain ⟨z,hz⟩ := sphere_immersion_tangent_surjective g hF hg hn hd
    (projectedPlaneMap_tangent (F x) a b hn.self_of_nhds (A,B))
  intro hzero
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L z) hzero
  rw [quadratic_profile_fderiv hF, hz] at hh
  have hba : inner ℝ b a = 0 := (real_inner_comm a b).trans hab
  simp only [zero_apply, projectedPlaneMap, LinearMap.comp_apply,
    tangentProjection_apply, planePairMap, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sub_right, inner_add_right, inner_smul_right, ha, hb, hab, hba] at hh
  have he : 2*((A^2+B^2)*(1-(A^2+B^2))) = 0 := by
    dsimp only [A,B] at hh ⊢
    rw [real_inner_comm (F x) a, real_inner_comm (F x) b] at hh
    nlinarith only [hh]
  have hp : 0 < 2*((A^2+B^2)*(1-(A^2+B^2))) :=
    mul_pos (by norm_num) (mul_pos hr₀ (sub_pos.mpr hr₁))
  linarith


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
open scoped Topology ContDiff
variable {n : ℕ}

lemma sphereChartMetric_pairing (g : SmoothMetric (Euclidean n) (Sphere n))
    (p : Sphere n) (y v w : Euclidean n) :
    (sphereChartMetric g p).inner y v w = chartMetricForm g p y v w := rfl

lemma sphereChartMetric_round (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg : IsRound g) (p : Sphere 3) (y v w : Euclidean 3) :
    (sphereChartMetric g p).inner y v w =
      inner ℝ (fderiv ℝ (roundChart (p : Euclidean 4) (sphereFrame p)) y v)
        (fderiv ℝ (roundChart (p : Euclidean 4) (sphereFrame p)) y w) := by
  rw [sphereChartMetric_pairing, chartMetricForm_pairing, hg]
  rw [sphere_coordinate_embedding, sphere_coordinate_embedding]
  rfl

lemma sphereChart_norm_sq (p : Sphere n) (y : Euclidean n) :
    inner ℝ (roundChart (p : Euclidean (n+1)) (sphereFrame p) y)
      (roundChart (p : Euclidean (n+1)) (sphereFrame p) y) = 1 := by
  rw [← sphere_chart_symm]
  have hh := ((chartAt (Euclidean n) p).symm y).property
  rw [Metric.mem_sphere, dist_zero_right] at hh
  rw [real_inner_self_eq_norm_sq, hh]
  norm_num

lemma sphericalBaseProfile_smooth (a b : Euclidean 4) (t : ℝ) :
    ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ (sphericalBaseProfile a b t) := by
  let : Fact (Module.finrank ℝ (Euclidean 4) = 3+1) := ⟨by simp [Euclidean]⟩
  unfold sphericalBaseProfile
  have h₁ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞
      (fun q : Sphere 3 => inner ℝ a (q : Euclidean 4)) :=
    (innerSL ℝ a).contDiff.contMDiff.comp contMDiff_coe_sphere
  have h₂ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞
      (fun q : Sphere 3 => inner ℝ b (q : Euclidean 4)) :=
    (innerSL ℝ b).contDiff.contMDiff.comp contMDiff_coe_sphere
  exact ((contMDiff_const.add (h₁.pow 2)).add (h₂.pow 2)).sub contMDiff_const

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

lemma sphericalBaseProfile_chart_fderiv_ne_zero (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg : IsRound g) (p : Sphere 3) (a b : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (t : ℝ) (y : Euclidean 3)
    (hr₀ : 0 < (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) a)^2 +
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) b)^2)
    (hr₁ : (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) a)^2 +
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) b)^2 < 1) :
    fderiv ℝ (sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm) y ≠ 0 := by
  rw [sphericalBaseProfile_chart_eq]
  exact sphere_quadratic_profile_fderiv_ne_zero (sphereChartMetric g p) (roundChart_smooth _ _)
    (sphereChartMetric_round g hg p y)
    (Filter.Eventually.of_forall (sphereChart_norm_sq p)) (by simp [Euclidean]) a b ha hb hab _ hr₀ hr₁


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

lemma sphericalBaseProfile_radius (a b : Euclidean 4) (t : ℝ) (q : Sphere 3) :
    sphericalBaseProfile a b t q = radialBaseEnvelope t (sphericalRadius a b q) := by
  rw [radialBaseEnvelope,sphericalRadius_sq]
  dsimp [sphericalBaseProfile]
  ring

lemma sphericalProfileGlue_chart (p : Sphere 3) (a b : Euclidean 4) (t : ℝ)
    (ψ : Euclidean 3 → ℝ) :
    sphericalProfileGlue p a b t ψ ∘ (chartAt (Euclidean 3) p).symm = ψ := by
  funext y
  dsimp only [sphericalProfileGlue,Function.comp_def]
  rw [manifoldChartPush_apply p _ (by rw [sphere_chart_target]; trivial)]
  ring

lemma sphericalProfileGlue_smooth (p : Sphere 3) (a b : Euclidean 4) (t : ℝ)
    {ψ : Euclidean 3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport (fun y => ψ y-
      sphericalBaseProfile a b t ((chartAt (Euclidean 3) p).symm y))) :
    ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ (sphericalProfileGlue p a b t ψ) :=
  (sphericalBaseProfile_smooth a b t).add
    (contMDiff_manifoldChartPush p (hψ.sub (sphericalBaseProfile_chart_smooth p a b t)) hc
      (by rw [sphere_chart_target]; exact subset_univ _))

lemma sphericalProfileGlue_sub (p : Sphere 3) (a b : Euclidean 4) (t : ℝ)
    (ψ : Euclidean 3 → ℝ) :
    (fun q => sphericalProfileGlue p a b t ψ q-sphericalBaseProfile a b t q) =
      manifoldChartPush p (fun y => ψ y-
        sphericalBaseProfile a b t ((chartAt (Euclidean 3) p).symm y)) := by
  funext q
  simp only [sphericalProfileGlue,add_sub_cancel_left]

lemma sphericalProfileGlue_tsupport (p : Sphere 3) (a b : Euclidean 4) (t : ℝ)
    {ψ : Euclidean 3 → ℝ}
    (hc : HasCompactSupport (fun y => ψ y-
      sphericalBaseProfile a b t ((chartAt (Euclidean 3) p).symm y)))
    {U : Set (Euclidean 3)} (hs : tsupport (fun y => ψ y-
      sphericalBaseProfile a b t ((chartAt (Euclidean 3) p).symm y)) ⊆ U) :
    tsupport (fun q => sphericalProfileGlue p a b t ψ q-sphericalBaseProfile a b t q) ⊆
      (chartAt (Euclidean 3) p).symm '' U := by
  rw [sphericalProfileGlue_sub]
  exact (manifoldChartPush_tsupport p hc (by rw [sphere_chart_target]; exact subset_univ _)).trans
    (image_mono hs)

lemma sphericalProfileGlue_close (p : Sphere 3) (a b : Euclidean 4) (t : ℝ)
    {ψ : Euclidean 3 → ℝ} {η : ℝ} (hη : 0 < η)
    (hclose : ∀ y, |ψ y-sphericalBaseProfile a b t ((chartAt (Euclidean 3) p).symm y)| < η) :
    ∀ q, |sphericalProfileGlue p a b t ψ q-sphericalBaseProfile a b t q| < η := by
  intro q
  have he := congrFun (sphericalProfileGlue_sub p a b t ψ) q
  rw [he]
  by_cases hq : q ∈ (chartAt (Euclidean 3) p).source
  · simpa only [manifoldChartPush,Set.indicator_of_mem hq,Function.comp_apply] using
      hclose ((chartAt (Euclidean 3) p) q)
  · simpa only [manifoldChartPush,Set.indicator_of_notMem hq,abs_zero] using hη

theorem spherical_envelope_perturbation {U : Set (Sphere 3)}
    (hU : ∀ q ∈ U, (1/20 : ℝ) < sphericalRadius sourceAxisOne sourceAxisTwo q ∧
      sphericalRadius sourceAxisOne sourceAxisTwo q < 1/8) :
    ∃ η > 0, ∀ t ∈ Icc (1/5 : ℝ) (3/10), ∀ φ : Sphere 3 → ℝ,
      tsupport (fun q => φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q) ⊆ U →
      (∀ q, |φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q| < η) →
      (∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
        sphericalRadius sourceAxisOne sourceAxisTwo q < t →
        Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q) ∧
      (∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
        φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) := by
  obtain ⟨η,hη,hmargin⟩ := radialBaseEnvelope_uniform_sign_margin
  refine ⟨η,hη,?_⟩
  intro t ht φ hs hclose
  have he (q : Sphere 3) (hq : q ∉ U) :
      φ q = sphericalBaseProfile sourceAxisOne sourceAxisTwo t q := by
    have hz : φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun z => φ z-
        sphericalBaseProfile sourceAxisOne sourceAxisTwo t z) (fun h => hq (hs h))
    linarith
  have ht0 : 0 < t := by linarith [ht.1]
  constructor
  · intro q hr hrt
    by_cases hq : q ∈ U
    · have hm := hmargin t ht (sphericalRadius sourceAxisOne sourceAxisTwo q)
        ⟨(hU q hq).1.le,(hU q hq).2.le⟩
      rw [← sphericalBaseProfile_radius] at hm
      have hl := (abs_lt.mp (hclose q)).1
      linarith
    · rw [he q hq,sphericalBaseProfile_radius]
      exact radialBaseEnvelope_inside ht0 ht.2 hr hrt
  · intro q htr
    have hq : q ∉ U := by
      intro hq
      have hh := (hU q hq).2
      linarith [ht.1]
    rw [he q hq,sphericalBaseProfile_radius]
    obtain ⟨ha,hb,hab⟩ := source_axes_orthonormal
    exact radialBaseEnvelope_outside ht0 ht.2 htr
      (sphericalRadius_le_one sourceAxisOne sourceAxisTwo ha hb hab q)



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ActualMetricSuperpositionSmallBall
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter
open scoped Topology ContDiff
section CoordinateProfiles
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma coordinateMetricGradient_pairing (g : SmoothMetric E E) (φ : E → ℝ) (p v : E) :
    selfMetricFlat g p (coordinateMetricGradient g φ p) v = fderiv ℝ φ p v := by
  have h := (selfMetricFlat_invertible g p).inverse_apply_eq.mp
    (show (selfMetricFlat g p).inverse (fderiv ℝ φ p) = coordinateMetricGradient g φ p from rfl)
  exact congrArg (fun l : E →L[ℝ] ℝ => l v) h.symm
end CoordinateProfiles

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal


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
open Set Filter
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma twoPlane_has_transverse (hd : Module.finrank ℝ E = 3)
    (P : Submodule ℝ E) (hP : Module.finrank ℝ P = 2) (q : E) :
    ∃ v : E, v ∈ P ∧ v ≠ 0 ∧ inner ℝ q v = 0 := by
  by_cases hq : q = 0
  · obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show 0 < Module.finrank ℝ P by omega)
    exact ⟨v,v.property,(fun h => hv (Subtype.ext h)),by simp [hq]⟩
  let K := (ℝ ∙ q)ᗮ
  let : Fact (Module.finrank ℝ E = 2+1) := ⟨hd⟩
  have hK : Module.finrank ℝ K = 2 := Submodule.finrank_orthogonal_span_singleton hq
  have hi := P.finrank_sup_add_finrank_inf_eq K
  have hu : Module.finrank ℝ (P ⊔ K : Submodule ℝ E) ≤ 3 :=
    (Submodule.finrank_le _).trans_eq hd
  obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank ℝ (P ⊓ K : Submodule ℝ E) by omega)
  exact ⟨v,v.property.1,(fun h => hv (Subtype.ext h)),
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property.2⟩

theorem metricProfileStrict_of_two_plane (hd : Module.finrank ℝ E = 3)
    (B H : CoordinateForm E) (a q : E)
    (hB : ∀ v, v ≠ 0 → 0 < B v v)
    (hlower : ∀ v, -(1/2 : ℝ)*B v v ≤ H v v)
    (hplane : ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, B v v ≤ H v v) :
    quadraticPlaneStrict (metricProfileTraceForm B H a) q := by
  obtain ⟨P,hP,hpos⟩ := hplane
  obtain ⟨v,hvP,hv,hq⟩ := twoPlane_has_transverse hd P hP q
  rw [quadraticPlaneStrict_iff_nonzero]
  refine ⟨v,hv,hq,?_⟩
  rw [metricProfileTraceForm_apply]
  have hvpos := hB v hv
  have hapos : 0 ≤ B a a := by
    by_cases ha : a = 0
    · simp [ha]
    · exact (hB a ha).le
  have h₁ := mul_le_mul_of_nonneg_left (hlower a) hvpos.le
  have h₂ := mul_le_mul_of_nonneg_left (hpos v hvP) (by linarith : 0 ≤ 1+B a a)
  nlinarith [mul_nonneg hvpos.le hapos]

theorem actualProfileStrict_of_two_plane (g : SmoothMetric E E)
    (hd : Module.finrank ℝ E = 3) (f : E → ℝ) (x : E)
    (hlower : ∀ v, -(1/2 : ℝ)*selfMetricFlat g x v v ≤ actualCoordinateHessian g f x v v)
    (hplane : ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, selfMetricFlat g x v v ≤ actualCoordinateHessian g f x v v) :
    actualProfileStrict g f x :=
  metricProfileStrict_of_two_plane hd _ _ _ _ (fun v hv => selfMetricFlat_pos g x (v := v) hv) hlower hplane


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

lemma sphericalRadius_chart_sq (p : Sphere 3) (a b : Euclidean 4) (y : Euclidean 3) :
    (sphericalRadius a b ((chartAt (Euclidean 3) p).symm y))^2 =
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) a)^2 +
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) b)^2 := by
  rw [sphericalRadius_sq,congrFun (sphere_chart_symm p) y]
  rw [real_inner_comm a,real_inner_comm b]

lemma hessianMargins_actualProfileStrict (g : SmoothMetric (Euclidean 3) (Euclidean 3))
    (f : Euclidean 3 → ℝ) (y : Euclidean 3)
    (h : hessianMargins (selfMetricFlat g y) (actualCoordinateHessian g f y)) :
    actualProfileStrict g f y :=
  actualProfileStrict_of_two_plane g (by simp [Euclidean]) f y
    (hessianMargins_lower h) (hessianMargins_plane h)

lemma hessianMargins_positive_two_plane (g : SmoothMetric (Euclidean 3) (Euclidean 3))
    (f : Euclidean 3 → ℝ) (y : Euclidean 3)
    (h : hessianMargins (selfMetricFlat g y) (actualCoordinateHessian g f y)) :
    ∃ P : Submodule ℝ (Euclidean 3), Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g f y v v := by
  obtain ⟨P,hP,hp⟩ := hessianMargins_plane h
  exact ⟨P,hP,fun v hv hv0 => (selfMetricFlat_pos g y hv0).trans_le (hp v hv)⟩



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

lemma sourceSignBox_band (y : NormalWaveSpace)
    (hy : y ∈ normalWaveEquiv '' Box.Icc sourceSignBox) :
    (1/20 : ℝ) < sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) ∧
    sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < 1/8 :=
  Classical.choose_spec exists_spherical_sign_box y hy

lemma sourceSignRegion_band (q : Sphere 3) (hq : q ∈ sourceSignRegion) :
    (1/20 : ℝ) < sphericalRadius sourceAxisOne sourceAxisTwo q ∧
      sphericalRadius sourceAxisOne sourceAxisTwo q < 1/8 := by
  obtain ⟨y,⟨x,hx,rfl⟩,rfl⟩ := hq
  exact sourceSignBox_band _ ⟨x,sourceSignBox.Ioo_subset_Icc hx,rfl⟩

lemma sourceSignBox_subset_coverage :
    normalWaveEquiv '' Box.Icc sourceSignBox ⊆ sourceProfileCoverage := by
  intro y hy
  apply (mem_sphericalCoverage_iff sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole (R := 3/10) (by norm_num) y).mpr
  have hh := (sourceSignBox_band y hy).2
  linarith

lemma coordinateMetricGradient_ne_zero_of_fderiv
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace) (f : NormalWaveSpace → ℝ)
    (y : NormalWaveSpace) (hf : fderiv ℝ f y ≠ 0) :
    coordinateMetricGradient g f y ≠ 0 := by
  intro hz
  apply hf
  ext v
  have hh := coordinateMetricGradient_pairing g f y v
  rw [hz] at hh
  simpa using hh.symm

lemma source_baseProfile_sign_gradient
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (t : ℝ) :
    ∀ y ∈ normalWaveEquiv '' Box.Icc sourceSignBox,
      coordinateMetricGradient (sphereChartMetric g sourcePole)
        (sphericalBaseProfile sourceAxisOne sourceAxisTwo t ∘
          (chartAt (Euclidean 3) sourcePole).symm) y ≠ 0 := by
  intro y hy
  obtain ⟨hr₀,hr₁⟩ := sourceSignBox_band y hy
  obtain ⟨ha,hb,hab⟩ := source_axes_orthonormal
  apply coordinateMetricGradient_ne_zero_of_fderiv
  apply sphericalBaseProfile_chart_fderiv_ne_zero g₀ hg₀ sourcePole
    sourceAxisOne sourceAxisTwo ha hb hab t y
  · rw [← sphericalRadius_chart_sq]
    nlinarith
  · rw [← sphericalRadius_chart_sq]
    have hn := sphericalRadius_nonneg sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y)
    nlinarith

theorem exists_global_spherical_wave_profile_oai
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    (t : ℝ) (ht : t ∈ Icc (1/5 : ℝ) (3/10)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ ∧
      tsupport (fun q => φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q) ⊆ sourceSignRegion ∧
      (∀ q, |φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q| < ε) ∧
      (∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
        sphericalRadius sourceAxisOne sourceAxisTwo q < t →
        Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q) ∧
      (∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
        φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) ∧
      (∀ y ∈ sourceProfileCoverage, fderiv ℝ (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y ≠ 0 →
        actualProfileStrict (sphereChartMetric g sourcePole)
          (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y) ∧
      (∀ y ∈ sourceProfileCoverage, fderiv ℝ (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y = 0 →
        ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
          ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian (sphereChartMetric g sourcePole)
            (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y v v) ∧
      (∀ y ∈ normalWaveEquiv '' Box.Icc sourceSignBox,
        coordinateMetricGradient (sphereChartMetric g sourcePole)
          (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y ≠ 0 ∧
        actualProfileStrict (sphereChartMetric g sourcePole)
          (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y) ∧
      T < ∫ x in Box.Icc sourceSignBox, profileFrequencyScale (sphereChartMetric g sourcePole)
        (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) (normalWaveEquiv x) := by
  let f := sphericalBaseProfile sourceAxisOne sourceAxisTwo t ∘
    (chartAt (Euclidean 3) sourcePole).symm
  let G := sphereChartMetric g sourcePole
  obtain ⟨η,hη,henvelope⟩ := spherical_envelope_perturbation sourceSignRegion_band
  have htol : 0 < min ε η := lt_min hε hη
  have hnc : ∀ y ∈ sourceProfileCoverage, fderiv ℝ f y ≠ 0 → actualProfileStrict G f y := by
    intro y hy _
    exact hessianMargins_actualProfileStrict G f y (hg t y hy)
  have hcrit : ∀ y ∈ sourceProfileCoverage, fderiv ℝ f y = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian G f y v v := by
    intro y hy _
    exact hessianMargins_positive_two_plane G f y (hg t y hy)
  obtain ⟨ψ,hψ,hc,hs,hclose,hinside,hncψ,hcritψ,hmass⟩ :=
    exists_global_box_amplified_profile G sourceSignBox
      (sphericalBaseProfile_chart_smooth sourcePole sourceAxisOne sourceAxisTwo t)
      hnc hcrit sourceSignBox_subset_coverage (source_baseProfile_sign_gradient g₀ hg₀ g t) T htol
  let φ := sphericalProfileGlue sourcePole sourceAxisOne sourceAxisTwo t ψ
  have hφ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ :=
    sphericalProfileGlue_smooth sourcePole sourceAxisOne sourceAxisTwo t hψ hc
  have hchart : φ ∘ (chartAt (Euclidean 3) sourcePole).symm = ψ :=
    sphericalProfileGlue_chart sourcePole sourceAxisOne sourceAxisTwo t ψ
  have hsp : tsupport (fun q => φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q) ⊆
      sourceSignRegion := sphericalProfileGlue_tsupport sourcePole sourceAxisOne sourceAxisTwo t hc hs
  have hcl := sphericalProfileGlue_close sourcePole sourceAxisOne sourceAxisTwo t htol hclose
  obtain ⟨hin,hout⟩ := henvelope t ht φ hsp (fun q => (hcl q).trans_le (min_le_right _ _))
  refine ⟨φ,hφ,hsp,(fun q => (hcl q).trans_le (min_le_left _ _)),hin,hout,?_,?_,?_,?_⟩
  · simpa only [hchart] using hncψ
  · simpa only [hchart] using hcritψ
  · simpa only [hchart] using hinside
  · simpa only [hchart] using hmass

end YauCounterexamples

end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_global_spherical_wave_profile_oai := @OAI.YauCounterexamples.exists_global_spherical_wave_profile_oai
