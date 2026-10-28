-- Prove2me | solution 1 for OAI.YauCounterexamples.sphericalBaseProfile_chart_margins
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:45:19.459358+00:00
-- url     : https://prove2.me/submissions/5bf45518-04f8-49e6-bdf1-9e89912de937

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

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

omit [FiniteDimensional ℝ E] in
lemma fderiv_induced_metric (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : E,
      g.inner y v w = inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w)) (v w z : E) :
    fderiv ℝ (selfMetricFlat g) x v w z =
      inner ℝ (fderiv ℝ (fderiv ℝ F) x v w) (fderiv ℝ F x z) +
      inner ℝ (fderiv ℝ F x w) (fderiv ℝ (fderiv ℝ F) x v z) := by
  have he : (fun y => selfMetricFlat g y w z) =ᶠ[𝓝 x]
      (fun y => inner ℝ (fderiv ℝ F y w) (fderiv ℝ F y z)) := by
    filter_upwards [hg] with y hy
    exact hy w z
  rw [← fderiv_metric_pairing, he.fderiv_eq]
  have hd := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  rw [fderiv_inner_apply _ ((hd x).clm_apply (differentiableAt_const w))
      ((hd x).clm_apply (differentiableAt_const z)),
    fderiv_fderiv_apply hF, fderiv_fderiv_apply hF]
  ring

lemma induced_metric_christoffel (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : E,
      g.inner y v w = inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w)) (v w z : E) :
    inner ℝ (fderiv ℝ F x (metricChristoffel g x v w)) (fderiv ℝ F x z) =
      inner ℝ (fderiv ℝ (fderiv ℝ F) x v w) (fderiv ℝ F x z) := by
  have hgx := hg.self_of_nhds
  rw [← hgx, ← selfMetricFlat_apply, metricChristoffel_pairing]
  simp only [fderiv_induced_metric g hF hg]
  have hs : IsSymmSndFDerivAt ℝ F x := hF.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))
  rw [hs w v, hs z v, hs z w,
    real_inner_comm (fderiv ℝ F x w) (fderiv ℝ (fderiv ℝ F) x v z)]
  ring

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

omit [FiniteDimensional ℝ E] in
lemma sphere_immersion_normal_second {F : E → V} (hF : ContDiff ℝ ∞ F) {x : E}
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1) (v w : E) :
    inner ℝ (F x) (fderiv ℝ (fderiv ℝ F) x v w) =
      -inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w) := by
  have he : (fun y => inner ℝ (F y) (fderiv ℝ F y w)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_eventually_nhds.2 hn] with y hy
    exact sphere_immersion_normal_first hF hy w
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) he.fderiv_eq
  have hd := hF.differentiable (by simp) x
  have hdd := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [fderiv_inner_apply ℝ hd (hdd.clm_apply (differentiableAt_const w)),
    fderiv_fderiv_apply hF] at hh
  simp only [fderiv_const_apply, zero_apply] at hh
  linarith

theorem sphere_immersion_gauss (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : E,
      g.inner y v w = inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hspan : ∀ b : V, ∃ z : E, ∃ t : ℝ, b = fderiv ℝ F x z + t • F x)
    (v w : E) :
    fderiv ℝ (fderiv ℝ F) x v w - fderiv ℝ F x (metricChristoffel g x v w) =
      -(selfMetricFlat g x v w) • F x := by
  apply ext_inner_right ℝ
  intro b
  obtain ⟨z,t,rfl⟩ := hspan b
  have hfirst (a : E) : inner ℝ (fderiv ℝ F x a) (F x) = 0 := by
    rw [real_inner_comm]
    exact sphere_immersion_normal_first hF hn a
  have hsecond : inner ℝ (fderiv ℝ (fderiv ℝ F) x v w) (F x) =
      -selfMetricFlat g x v w := by
    rw [real_inner_comm, sphere_immersion_normal_second hF hn,
      ← hg.self_of_nhds v w]
    rfl
  simp only [inner_add_right, inner_smul_right, inner_sub_left, real_inner_smul_left]
  rw [induced_metric_christoffel g hF hg, hfirst, hsecond,
    sphere_immersion_normal_first hF hn, hn.self_of_nhds]
  ring

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

lemma projectedPlaneMap_norm_sq (p a b : V) (hp : inner ℝ p p = 1)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (c : ℝ × ℝ) :
    inner ℝ (projectedPlaneMap p a b c) (projectedPlaneMap p a b c) =
      c.1^2 + c.2^2 - (c.1 * inner ℝ p a + c.2 * inner ℝ p b)^2 := by
  simp only [projectedPlaneMap, LinearMap.comp_apply, tangentProjection_apply,
    planePairMap, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, inner_smul_right, hp, ha, hb, hab,
    show inner ℝ b a = 0 from (real_inner_comm a b).trans hab,
    real_inner_comm a p, real_inner_comm b p]
  ring

lemma projectedPlaneMap_quadratic (p a b : V) (hp : inner ℝ p p = 1)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (c : ℝ × ℝ) :
    (inner ℝ a (projectedPlaneMap p a b c))^2 +
        (inner ℝ b (projectedPlaneMap p a b c))^2 =
      c.1^2+c.2^2 - (2-((inner ℝ p a)^2+(inner ℝ p b)^2))*
        (c.1*inner ℝ p a+c.2*inner ℝ p b)^2 := by
  calc
    _ = inner ℝ (projectedPlaneMap p a b c) (projectedPlaneMap p a b c) -
        (1-((inner ℝ p a)^2+(inner ℝ p b)^2))*
          (c.1*inner ℝ p a+c.2*inner ℝ p b)^2 := by
      simp only [projectedPlaneMap, LinearMap.comp_apply, tangentProjection_apply,
        planePairMap, LinearMap.coe_mk, AddHom.coe_mk,
        inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
        real_inner_smul_left, inner_smul_right, hp, ha, hb, hab,
        show inner ℝ b a = 0 from (real_inner_comm a b).trans hab,
        real_inner_comm a p, real_inner_comm b p]
      ring
    _ = _ := by
      rw [projectedPlaneMap_norm_sq p a b hp ha hb hab]
      ring

lemma plane_cauchy (A B s t : ℝ) :
    (s*A+t*B)^2 ≤ (A^2+B^2)*(s^2+t^2) := by
  nlinarith [sq_nonneg (s*B-t*A)]

lemma projectedPlaneMap_lower (p a b : V) (hp : inner ℝ p p = 1)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (c : ℝ × ℝ) :
    (1-((inner ℝ p a)^2+(inner ℝ p b)^2))*(c.1^2+c.2^2) ≤
      inner ℝ (projectedPlaneMap p a b c) (projectedPlaneMap p a b c) := by
  rw [projectedPlaneMap_norm_sq p a b hp ha hb hab]
  nlinarith [plane_cauchy (inner ℝ p a) (inner ℝ p b) c.1 c.2]

lemma projectedPlaneMap_injective (p a b : V) (hp : inner ℝ p p = 1)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (hr : (inner ℝ p a)^2+(inner ℝ p b)^2 < 1) :
    Function.Injective (projectedPlaneMap p a b) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro c hc
  have hz : projectedPlaneMap p a b c = 0 := hc
  have hh := projectedPlaneMap_lower p a b hp ha hb hab c
  rw [hz, inner_zero_left] at hh
  have hq : c.1^2+c.2^2 = 0 := by
    nlinarith [sq_nonneg c.1, sq_nonneg c.2]
  have h₁ : c.1 = 0 := by nlinarith [sq_nonneg c.2]
  have h₂ : c.2 = 0 := by nlinarith [sq_nonneg c.1]
  exact Prod.ext h₁ h₂

lemma projectedPlaneMap_quadratic_lower (p a b : V) (hp : inner ℝ p p = 1)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (c : ℝ × ℝ) :
    (1-((inner ℝ p a)^2+(inner ℝ p b)^2))*
        inner ℝ (projectedPlaneMap p a b c) (projectedPlaneMap p a b c) ≤
      (inner ℝ a (projectedPlaneMap p a b c))^2 +
        (inner ℝ b (projectedPlaneMap p a b c))^2 := by
  rw [projectedPlaneMap_quadratic p a b hp ha hb hab,
    projectedPlaneMap_norm_sq p a b hp ha hb hab]
  nlinarith [plane_cauchy (inner ℝ p a) (inner ℝ p b) c.1 c.2]

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

omit [FiniteDimensional ℝ E] in
lemma fderiv_clm_comp_apply (L : V →L[ℝ] ℝ) {F : E → V}
    (hF : ContDiff ℝ ∞ F) (x v : E) :
    fderiv ℝ (fun y => L (F y)) x v = L (fderiv ℝ F x v) := by
  change (fderiv ℝ (L ∘ F) x) v = _
  rw [(L.hasFDerivAt.comp x ((hF.differentiable (by simp) x).hasFDerivAt)).fderiv]
  rfl

omit [FiniteDimensional ℝ E] in
lemma fderiv_second_clm_comp_apply (L : V →L[ℝ] ℝ) {F : E → V}
    (hF : ContDiff ℝ ∞ F) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => L (F y))) x v w =
      L (fderiv ℝ (fderiv ℝ F) x v w) := by
  have hLF : ContDiff ℝ ∞ (fun y => L (F y)) := L.contDiff.comp hF
  rw [← fderiv_fderiv_apply hLF]
  simp_rw [fderiv_clm_comp_apply L hF]
  rw [fderiv_clm_comp_apply L
    ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const),
    fderiv_fderiv_apply hF]

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

lemma actualCoordinateHessian_square (g : SmoothMetric E E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (x v w : E) :
    actualCoordinateHessian g (fun y => (f y)^2) x v w =
      2 * (fderiv ℝ f x v) * (fderiv ℝ f x w) +
      2 * f x * actualCoordinateHessian g f x v w := by
  have hfd := hf.differentiable (by simp)
  have hff : ContDiff ℝ ∞ (fun y => (f y)^2) := hf.pow 2
  have he (y z : E) : fderiv ℝ (fun s => (f s)^2) y z =
      2 * f y * fderiv ℝ f y z := by
    simp only [pow_two]
    rw [fderiv_fun_mul (hfd y) (hfd y)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [actualCoordinateHessian_apply, ← fderiv_fderiv_apply hff]
  simp_rw [he]
  have hdf : ContDiff ℝ ∞ (fun y => fderiv ℝ f y w) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [fderiv_fun_mul ((contDiff_const.mul hf).differentiable (by simp) x)
      (hdf.differentiable (by simp) x),
    fderiv_fun_mul (differentiableAt_const _) (hfd x)]
  simp only [add_apply, smul_apply, smul_eq_mul, fderiv_const_apply, zero_apply]
  rw [fderiv_fderiv_apply hf, actualCoordinateHessian_apply]
  ring

end ScalarHessian
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem sphere_coordinate_hessian (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : E,
      g.inner y v w = inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1)
    (L : V →L[ℝ] ℝ) (v w : E) :
    actualCoordinateHessian g (fun y => L (F y)) x v w =
      -L (F x) * selfMetricFlat g x v w := by
  rw [actualCoordinateHessian_apply, fderiv_clm_comp_apply L hF,
    fderiv_second_clm_comp_apply L hF, ← map_sub]
  rw [sphere_immersion_gauss g hF hg hn
    (sphere_immersion_spans g hF hg.self_of_nhds hn hd)]
  simp only [map_smul, smul_eq_mul]
  ring

theorem sphere_quadratic_profile_hessian (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : E,
      g.inner y v w = inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1)
    (L₁ L₂ : V →L[ℝ] ℝ) (c : ℝ) (v w : E) :
    actualCoordinateHessian g (fun y => c + (L₁ (F y))^2 + (L₂ (F y))^2) x v w =
      2 * (L₁ (fderiv ℝ F x v) * L₁ (fderiv ℝ F x w) +
        L₂ (fderiv ℝ F x v) * L₂ (fderiv ℝ F x w)) -
      2 * ((L₁ (F x))^2 + (L₂ (F x))^2) * selfMetricFlat g x v w := by
  have h₁ : ContDiff ℝ ∞ (fun y => L₁ (F y)) := L₁.contDiff.comp hF
  have h₂ : ContDiff ℝ ∞ (fun y => L₂ (F y)) := L₂.contDiff.comp hF
  rw [actualCoordinateHessian_add g (contDiff_const.add (h₁.pow 2)) (h₂.pow 2),
    actualCoordinateHessian_add g contDiff_const (h₁.pow 2),
    actualCoordinateHessian_const, actualCoordinateHessian_square g h₁,
    actualCoordinateHessian_square g h₂,
    sphere_coordinate_hessian g hF hg hn hd L₁,
    sphere_coordinate_hessian g hF hg hn hd L₂]
  simp only [fderiv_clm_comp_apply L₁ hF, fderiv_clm_comp_apply L₂ hF]
  ring

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

omit [FiniteDimensional ℝ E] in
theorem sphere_immersion_quadratic_two_plane (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ v w : E, g.inner x v w = inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1)
    (a b : V) (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1)
    (hab : inner ℝ a b = 0) (hr : (inner ℝ (F x) a)^2+(inner ℝ (F x) b)^2 < 1) :
    ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, (1-((inner ℝ (F x) a)^2+(inner ℝ (F x) b)^2))*g.inner x v v ≤
        (inner ℝ a (fderiv ℝ F x v))^2+(inner ℝ b (fderiv ℝ F x v))^2 := by
  obtain ⟨za,hza⟩ := sphere_immersion_tangent_surjective g hF hg hn hd
    (projectedPlaneMap_tangent (F x) a b hn.self_of_nhds (1,0))
  obtain ⟨zb,hzb⟩ := sphere_immersion_tangent_surjective g hF hg hn hd
    (projectedPlaneMap_tangent (F x) a b hn.self_of_nhds (0,1))
  let S := planePairMap za zb
  have hS : ∀ c, fderiv ℝ F x (S c) = projectedPlaneMap (F x) a b c := by
    intro c
    change fderiv ℝ F x (c.1 • za+c.2 • zb) = _
    rw [map_add, map_smul, map_smul, hza, hzb]
    have he : c = c.1 • ((1,0) : ℝ × ℝ)+c.2 • ((0,1) : ℝ × ℝ) := by ext <;> simp
    conv_rhs => rw [he]
    rw [map_add, map_smul, map_smul]
  have hinj : Function.Injective S := by
    intro c d he
    apply projectedPlaneMap_injective (F x) a b hn.self_of_nhds ha hb hab hr
    rw [← hS, ← hS, he]
  refine ⟨LinearMap.range S, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj]
    simp
  · rintro _ ⟨c,rfl⟩
    rw [hg, hS]
    exact projectedPlaneMap_quadratic_lower (F x) a b hn.self_of_nhds ha hb hab c

theorem sphere_quadratic_hessian_margins_strong (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : E, g.inner y v w =
      inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1)
    (a b : V) (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1)
    (hab : inner ℝ a b = 0) (C : ℝ)
    (hr : (inner ℝ (F x) a)^2+(inner ℝ (F x) b)^2 ≤ 1/8) :
    let f := fun y => C+(inner ℝ a (F y))^2+(inner ℝ b (F y))^2
    (∀ v, -(1/4 : ℝ)*selfMetricFlat g x v v ≤ actualCoordinateHessian g f x v v) ∧
    (∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, (3/2 : ℝ)*selfMetricFlat g x v v ≤ actualCoordinateHessian g f x v v) := by
  intro f
  have hess := sphere_quadratic_profile_hessian g hF hg hn hd (innerSL ℝ a) (innerSL ℝ b) C
  simp only [innerSL_apply_apply] at hess
  have hpos : ∀ (v : E), 0 ≤ g.inner x v v := by
    intro v
    rw [hg.self_of_nhds v v]
    exact real_inner_self_nonneg
  have hr' : (inner ℝ a (F x))^2+(inner ℝ b (F x))^2 ≤ 1/8 := by
    simpa only [real_inner_comm a (F x), real_inner_comm b (F x)] using hr
  constructor
  · intro v
    dsimp only [f]
    rw [hess v v]
    rw [selfMetricFlat_apply]
    simp only [← sq]
    nlinarith [mul_le_mul_of_nonneg_right hr' (hpos v),
      sq_nonneg (inner ℝ a (fderiv ℝ F x v)), sq_nonneg (inner ℝ b (fderiv ℝ F x v))]
  · obtain ⟨P,hP,hbound⟩ := sphere_immersion_quadratic_two_plane g hF hg.self_of_nhds hn hd
      a b ha hb hab (by linarith)
    refine ⟨P,hP,?_⟩
    intro v hv
    have hh := hbound v hv
    dsimp only [f]
    rw [hess v v]
    rw [selfMetricFlat_apply]
    simp only [← sq]
    change (3/2 : ℝ)*g.inner x v v ≤
      2*((inner ℝ a (fderiv ℝ F x v))^2+(inner ℝ b (fderiv ℝ F x v))^2)-
      2*((inner ℝ a (F x))^2+(inner ℝ b (F x))^2)*g.inner x v v
    rw [real_inner_comm a (F x), real_inner_comm b (F x)] at hh
    nlinarith [mul_le_mul_of_nonneg_right hr' (hpos v)]

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

lemma sphericalBaseProfile_chart_eq (p : Sphere 3) (a b : Euclidean 4) (t : ℝ) :
    sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm =
      fun z => (Real.log t-t^2) +
        (inner ℝ a (roundChart (p : Euclidean 4) (sphereFrame p) z))^2 +
        (inner ℝ b (roundChart (p : Euclidean 4) (sphereFrame p) z))^2 := by
  funext z
  dsimp [Function.comp_def, sphericalBaseProfile]
  rw [congrFun (sphere_chart_symm p) z]
  ring

theorem sphericalBaseProfile_chart_margins_oai (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg : IsRound g) (p : Sphere 3) (a b : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (t : ℝ) (y : Euclidean 3)
    (hr : (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) a)^2 +
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) b)^2 ≤ 1/8) :
    let G := sphereChartMetric g p
    let f := sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm
    (∀ v, -(1/4 : ℝ)*selfMetricFlat G y v v ≤ actualCoordinateHessian G f y v v) ∧
    (∃ P : Submodule ℝ (Euclidean 3), Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, (3/2 : ℝ)*selfMetricFlat G y v v ≤ actualCoordinateHessian G f y v v) := by
  dsimp only
  rw [sphericalBaseProfile_chart_eq]
  exact sphere_quadratic_hessian_margins_strong (sphereChartMetric g p) (roundChart_smooth _ _)
    (Filter.Eventually.of_forall (sphereChartMetric_round g hg p))
    (Filter.Eventually.of_forall (sphereChart_norm_sq p)) (by simp [Euclidean]) a b ha hb hab _ hr


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

theorem solution : type_of% @OAI.YauCounterexamples.sphericalBaseProfile_chart_margins_oai := @OAI.YauCounterexamples.sphericalBaseProfile_chart_margins_oai
