-- Prove2me | solution 1 for OAI.YauCounterexamples.compact_actual_waves_sign_and_jets_supported
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:03:07.057805+00:00
-- url     : https://prove2.me/submissions/6c25b2ef-abb8-4048-a6fd-60b10b0f62b8

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_compact_metric_packet_sign_gain
import Theorems.Thm_OAI_YauCounterexamples_metric_center_polynomial_net_with_coverage
import Theorems.Thm_OAI_YauCounterexamples_physical_finite_superposition_complete_supported

section
-- module Solutions.OAIQ070_YAU.Compat
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

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

attribute [local instance] OAI.YauCounterexamples.metricDualNorm
attribute [local instance] OAI.YauCounterexamples.metricDualSpace
attribute [local instance] OAI.YauCounterexamples.metricFormNorm
attribute [local instance] OAI.YauCounterexamples.metricFormSpace
attribute [local instance] OAI.YauCounterexamples.metricTriNorm
attribute [local instance] OAI.YauCounterexamples.metricTriSpace
omit [FiniteDimensional ℝ E] in
lemma fderiv_selfMetricFlat_symm (g : SmoothMetric E E) (x v w z : E) :
    fderiv ℝ (selfMetricFlat g) x v w z = fderiv ℝ (selfMetricFlat g) x v z w := by
  have hd := (contDiff_selfMetricFlat g).differentiable (by simp)
  have he : (fun y => selfMetricFlat g y w z) = (fun y => selfMetricFlat g y z w) :=
    funext (fun y => selfMetricFlat_symm g y w z)
  have h := congrArg (fun f : E → ℝ => fderiv ℝ f x v) he
  have heval (w z : E) : fderiv ℝ (fun y => selfMetricFlat g y w z) x v =
      fderiv ℝ (selfMetricFlat g) x v w z := by
    rw [fderiv_clm_apply ((hd x).clm_apply (differentiableAt_const w))
        (differentiableAt_const z),
      fderiv_clm_apply (hd x) (differentiableAt_const w)]
    simp
  simpa only [heval] using h

lemma metricChristoffel_symm (g : SmoothMetric E E) (x v w : E) :
    metricChristoffel g x v w = metricChristoffel g x w v := by
  apply (selfMetricFlat_invertible g x).injective
  ext z
  rw [metricChristoffel_pairing,metricChristoffel_pairing,
    fderiv_selfMetricFlat_symm g x z v w]
  ring


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalJetMapFirstPhase
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.normalDualNorm
attribute [local instance] OAI.YauCounterexamples.normalFormNorm
attribute [local instance] OAI.YauCounterexamples.normalDualSpace
attribute [local instance] OAI.YauCounterexamples.normalFormSpace
local instance normalTriNorm_r30eb4a_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma contDiff_normalJetMap (p : E) (A : E →L[ℝ] E) (C : E →L[ℝ] E →L[ℝ] E) :
    ContDiff ℝ ∞ (normalJetMap p A C) :=
  (contDiff_const.add A.contDiff).sub ((C.contDiff.clm_apply contDiff_id).const_smul (1/2 : ℝ))

omit [FiniteDimensional ℝ E] in
lemma normalJetMap_zero (p : E) (A : E →L[ℝ] E) (C : E →L[ℝ] E →L[ℝ] E) :
    normalJetMap p A C 0 = p := by simp [normalJetMap]

omit [FiniteDimensional ℝ E] in
lemma hasFDerivAt_normalJetMap (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (hC : ∀ v w, C v w = C w v) (x : E) :
    HasFDerivAt (normalJetMap p A C) (A - C x) x := by
  have h := ((hasFDerivAt_const p x).add A.hasFDerivAt).sub
    ((C.hasFDerivAt.clm_apply (hasFDerivAt_id x)).const_smul (1/2 : ℝ))
  change HasFDerivAt (fun y => p + A y - (1/2 : ℝ) • C y y) (A - C x) x
  apply h.congr_fderiv
  ext v
  simp only [_root_.sub_apply, _root_.add_apply,
    zero_add, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, id_eq, hC v x, ← two_smul ℝ, smul_smul]
  norm_num

omit [FiniteDimensional ℝ E] in
lemma fderiv_normalJetMap (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (hC : ∀ v w, C v w = C w v) (x : E) :
    fderiv ℝ (normalJetMap p A C) x = A - C x :=
  (hasFDerivAt_normalJetMap p A C hC x).fderiv


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
open Set Filter Manifold
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma normalJetMap_first_phase_jet (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (hC : ∀ v w, C v w = C w v)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (v : E) :
    fderiv ℝ (φ ∘ normalJetMap p A C) 0 v = fderiv ℝ φ p (A v) := by
  rw [fderiv_comp 0 (hφ.differentiable (by simp) _)
    ((contDiff_normalJetMap p A C).differentiable (by simp) _),fderiv_normalJetMap _ _ _ hC]
  simp [normalJetMap_zero]

omit [FiniteDimensional ℝ E] in
lemma normalJetMap_second_phase_jet (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (hC : ∀ v w, C v w = C w v)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (v w : E) :
    fderiv ℝ (fderiv ℝ (φ ∘ normalJetMap p A C)) 0 v w =
      fderiv ℝ (fderiv ℝ φ) p (A v) (A w) - fderiv ℝ φ p (C v w) := by
  let F := normalJetMap p A C
  have he : fderiv ℝ (φ ∘ F) = fun y => (fderiv ℝ φ (F y)).comp (A-C y) := by
    funext y
    rw [fderiv_comp y (hφ.differentiable (by simp) _) ((contDiff_normalJetMap p A C).differentiable (by simp) _)]
    rw [fderiv_normalJetMap _ _ _ hC]
  have hF : HasFDerivAt F A 0 := by
    simpa only [map_zero,sub_zero] using hasFDerivAt_normalJetMap p A C hC 0
  have hd := ((hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) (F 0)).hasFDerivAt
  have hA := (hasFDerivAt_const A (0 : E)).sub C.hasFDerivAt
  have hh := ((hd.comp 0 hF).clm_comp hA).fderiv
  simp only [Function.comp_def, Pi.sub_apply] at hh
  rw [he,hh]
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,map_zero,
    sub_zero,zero_sub,_root_.neg_apply,normalJetMap_zero,F]
  simp [sub_eq_add_neg,add_comm]

lemma metricNormal_second_phase_jet (g : SmoothMetric E E) (p : E) (A : E →L[ℝ] E)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (v w : E) :
    fderiv ℝ (fderiv ℝ (φ ∘ normalJetMap p A ((metricChristoffel g p).bilinearComp A A))) 0 v w =
      fderiv ℝ (fderiv ℝ φ) p (A v) (A w) -
        fderiv ℝ φ p (metricChristoffel g p (A v) (A w)) :=
  normalJetMap_second_phase_jet p A ((metricChristoffel g p).bilinearComp A A)
    (fun v w => metricChristoffel_symm g p (A v) (A w)) hφ v w


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_FrameDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
open Set
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma metricFrameSet_injective (g : SmoothMetric E E) {K : Set E}
    {q : E × (E →L[ℝ] E)} (hq : q ∈ metricFrameSet g K) : Function.Injective q.2 := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change q.2 v = 0 at hv
  have h := hq.2 v v
  rw [hv, map_zero] at h
  exact inner_self_eq_zero.mp h.symm

lemma metricFrameSet_equiv (g : SmoothMetric E E) {K : Set E}
    {q : E × (E →L[ℝ] E)} (hq : q ∈ metricFrameSet g K) :
    ∃ A : E ≃L[ℝ] E, (A : E →L[ℝ] E) = q.2 := by
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective q.2.toLinearMap
    ((LinearMap.injective_iff_surjective).mp (metricFrameSet_injective g hq) |>
      fun hs => ⟨metricFrameSet_injective g hq,hs⟩)
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ActualMetricSuperpositionSmallBall
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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

lemma normalWaveProfile_gradient_pairing
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (q : NormalWaveParameter)
    (v : NormalWaveSpace) :
    inner ℝ (gradient (normalWaveProfile g φ q) 0) v = fderiv ℝ φ q.1 (q.2 v) := by
  rw [inner_gradient_left]
  exact normalJetMap_first_phase_jet q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)
    (fun v w => metricChristoffel_symm g q.1 (q.2 v) (q.2 w)) hφ v

lemma normalWaveProfile_hessian
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (q : NormalWaveParameter)
    (v w : NormalWaveSpace) :
    actualHessianForm (normalWaveProfile g φ q) v w =
      actualCoordinateHessian g φ q.1 (q.2 v) (q.2 w) := by
  exact metricNormal_second_phase_jet g q.1 q.2 hφ v w

lemma metric_frame_gradient
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) {K : Set NormalWaveSpace}
    {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K) :
    q.2 (gradient (normalWaveProfile g φ q) 0) = coordinateMetricGradient g φ q.1 := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  apply (selfMetricFlat_invertible g q.1).injective
  ext w
  obtain ⟨v,rfl⟩ := A.surjective w
  have hAv : A v = q.2 v := congrArg (fun L : NormalWaveSpace →L[ℝ] NormalWaveSpace => L v) hA
  rw [hAv,hq.2,coordinateMetricGradient_pairing]
  exact normalWaveProfile_gradient_pairing g hφ q v

lemma actualProfileStrict_normal_direction
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) {K : Set NormalWaveSpace}
    {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K)
    (hs : actualProfileStrict g φ q.1) :
    ∃ b : PhaseSpace,
      inner ℝ (gradient (normalWaveProfile g φ q) 0) b = 0 ∧
      ‖b‖^2 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 ∧
      0 < actualHessianForm (normalWaveProfile g φ q) (gradient (normalWaveProfile g φ q) 0)
        (gradient (normalWaveProfile g φ q) 0)+actualHessianForm (normalWaveProfile g φ q) b b := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  obtain ⟨v,hv,hav,hpos⟩ := hs
  let w := A.symm v
  let a := gradient (normalWaveProfile g φ q) 0
  let H := actualHessianForm (normalWaveProfile g φ q)
  have hAw : q.2 w = v := by rw [←hA]; exact A.apply_symm_apply v
  have hAa : q.2 a = coordinateMetricGradient g φ q.1 := metric_frame_gradient g hφ hq
  have hw : w ≠ 0 := by
    intro hw0
    have hv0 : v = 0 := by rw [←hAw,hw0,map_zero]
    rw [hv0,norm_zero] at hv
    norm_num at hv
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hwperp : inner ℝ a w = 0 := by
    rw [normalWaveProfile_gradient_pairing g hφ q w,hAw]
    simpa only [InnerProductSpace.toDual_symm_apply] using hav
  have hmetric (y : NormalWaveSpace) : selfMetricFlat g q.1 (q.2 y) (q.2 y) = ‖y‖^2 := by
    rw [hq.2,real_inner_self_eq_norm_sq]
  have htrace : 0 < ‖w‖^2*H a a+(1+‖a‖^2)*H w w := by
    change 0 < metricProfileTraceForm _ _ _ v v at hpos
    rw [metricProfileTraceForm_apply,←hAw,←hAa,hmetric,hmetric] at hpos
    simpa only [←normalWaveProfile_hessian g hφ q] using hpos
  let L := Real.sqrt (1+‖a‖^2)
  have hL0 : 0 < L := Real.sqrt_pos.mpr (by positivity)
  have hLsq : L^2 = 1+‖a‖^2 := Real.sq_sqrt (by positivity)
  let b := (L/‖w‖) • w
  have hbsq : ‖b‖^2 = 1+‖a‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hL0 hwn),mul_pow,div_pow]
    field_simp
    exact hLsq
  refine ⟨b,?_,hbsq,?_⟩
  · change inner ℝ a ((L/‖w‖) • w) = 0
    rw [inner_smul_right,hwperp,mul_zero]
  · have hbH : H b b = (L/‖w‖)^2*H w w := by
      dsimp only [b]
      rw [show H ((L/‖w‖) • w) = (L/‖w‖) • H w from H.map_smul _ _]
      change (L/‖w‖)*(H w ((L/‖w‖) • w)) = _
      rw [(H w).map_smul]
      change (L/‖w‖)*((L/‖w‖)*H w w) = _
      ring
    have heq : ‖w‖^2*(H a a+H b b) = ‖w‖^2*H a a+(1+‖a‖^2)*H w w := by
      rw [hbH,div_pow]
      field_simp
      rw [hLsq]
      ring
    change 0 < H a a+H b b
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hwn)).mp (heq.symm ▸ htrace)

lemma actualCriticalPlane_normal
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) {K : Set NormalWaveSpace}
    {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K)
    (hc : ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ q.1 v v) :
    ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (normalWaveProfile g φ q) v v := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  obtain ⟨P,hP,hpos⟩ := hc
  refine ⟨P.map A.symm.toLinearEquiv.toLinearMap,?_,?_⟩
  · exact (A.symm.toLinearEquiv.finrank_map_eq P).trans hP
  · intro v hv hv0
    obtain ⟨w,hw,rfl⟩ := hv
    rw [normalWaveProfile_hessian g hφ q,←hA]
    change 0 < actualCoordinateHessian g φ q.1 (A (A.symm w)) (A (A.symm w))
    rw [A.apply_symm_apply]
    exact hpos w hw (by intro h; apply hv0; simp [h])
end

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
lemma normalWaveProfile_gradient_zero_iff
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) {K : Set NormalWaveSpace}
    {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K) :
    gradient (normalWaveProfile g φ q) 0 = 0 ↔ fderiv ℝ φ q.1 = 0 := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  constructor
  · intro ha
    ext v
    obtain ⟨w,rfl⟩ := A.surjective v
    have h := normalWaveProfile_gradient_pairing g hφ q w
    rw [ha,inner_zero_left] at h
    have hv : A w = q.2 w := congrArg (fun L : NormalWaveSpace →L[ℝ] NormalWaveSpace => L w) hA
    simpa only [hv,_root_.zero_apply] using h.symm
  · intro h
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [normalWaveProfile_gradient_pairing g hφ q,h,_root_.zero_apply]
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ActualMetricSuperpositionCompleteSupported
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples
theorem actual_metric_superposition_complete_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O)
    (hnc : ∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x)
    (hcrit : ∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v)
    (m D : ℕ) :
    ∃ ρ > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
    ∃ T > 0, ∃ c > 0, ∃ M₀ > 0, ∃ C > 0, ∃ r₀ > 0, ∃ rₑ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ n : ℝ, N ≤ n →
      ∃ (z : metricFrameSet g K → Fin 3 → Fin 3 → ℂ)
        (U : metricFrameSet g K → Fin 3 → NormalWaveSpace → ℂ),
        (∀ q ℓ, tsupport (U q ℓ) ⊆ O) ∧
        (∀ q ℓ, (∑ i, z q ℓ i*z q ℓ i = -1) ∧
          ‖phaseRealVector (z q ℓ)-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
        (∀ q ℓ, ContDiff ℝ ∞ (U q ℓ) ∧ HasCompactSupport (U q ℓ) ∧
          U q ℓ q.1.1 = Complex.exp ((n : ℂ)*(φ q.1.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U q ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1.1‖^2) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q ℓ) w +
              (n : ℂ)*((n : ℂ)+2)*U q ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        (∀ q ℓ (r : ℝ), 0 ≤ r → r < rₑ → (Real.sqrt n)⁻¹ ≤ r →
          ∀ x y : NormalWaveSpace, ‖x-q.1.1‖ ≤ r → ‖y-q.1.1‖ ≤ r → n*‖y-x‖ ≤ 1 →
          ‖U q ℓ y-(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector q (z q ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U q ℓ x‖ ≤
          (M₀*r)*‖(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector q (z q ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U q ℓ x‖) ∧
        ∀ (I : Type) [Fintype I] (p : I → metricFrameSet g K)
          (w : NormalWaveSpace → ℝ), ContDiff ℝ ∞ w → ∀ i₀ : I,
        ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
        let y := normalCoordinateMap g (p i₀) x
        ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*φ (normalWaveEquiv y)) →
        let W := Real.exp (n*φ (normalWaveEquiv y))+R
        ∀ r : ℝ, 0 ≤ r →
        (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {γ | ‖realWaveJet n W (finiteWaveSuperposition (w ∘ normalWaveEquiv)
            (fun i ℓ => U (p i) ℓ ∘ normalWaveEquiv) γ) y‖ ≤ r} ≤
          ENNReal.ofReal (C*n^28*r^4) := by
  apply physical_finite_superposition_complete_supported g φ hφ hK hO hKO _ _ m D
  · intro q hq ha
    apply actualProfileStrict_normal_direction g hφ hq
    exact hnc q.1 hq.1 (mt (normalWaveProfile_gradient_zero_iff g hφ hq).mpr ha)
  · intro q hq ha
    exact actualCriticalPlane_normal g hφ hq (hcrit q.1 hq.1
      ((normalWaveProfile_gradient_zero_iff g hφ hq).mp ha))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ExistsSmoothComplexCutoff
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
open Set
open Set Filter
open scoped Topology ContDiff Manifold
namespace YauCounterexamples

lemma exists_smooth_complex_cutoff (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ Metric.ball 0 ρ ∧ ζ =ᶠ[𝓝 0] (fun _ => 1) := by
  have hsub : ({(0 : Fin 3 → ℝ)} : Set (Fin 3 → ℝ)) ⊆
      interior (Metric.closedBall 0 (ρ/2)) := by
    rw [interior_closedBall _ (ne_of_gt (half_pos hρ))]
    exact singleton_subset_iff.mpr (Metric.mem_ball_self (half_pos hρ))
  obtain ⟨f,hf1,hf0,hfI⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ,Fin 3 → ℝ)) (n := ⊤) isClosed_singleton hsub
  let ζ : (Fin 3 → ℝ) → ℂ := fun x => (f x : ℂ)
  have hs : tsupport ζ ⊆ Metric.closedBall 0 (ρ/2) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra h
    exact hx (by simp [ζ,hf0 x h])
  refine ⟨ζ,Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.mp f.contMDiff),
    (isCompact_closedBall 0 (ρ/2)).of_isClosed_subset isClosed_closure hs,
    hs.trans (Metric.closedBall_subset_ball (half_lt_self hρ)),?_⟩
  have hh : ∀ᶠ x in 𝓝 (0 : Fin 3 → ℝ), f x = 1 := by simpa using hf1
  filter_upwards [hh] with x hx
  simp [ζ,hx]

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactActualMetricPacketsSupported
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples
theorem compact_actual_metric_packets_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O)
    (hnc : ∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x)
    (hcrit : ∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v)
    (m D : ℕ) :
    ∃ T > 0, ∃ c > 0, ∃ M > 0, ∃ C > 0, ∃ Q > 0, ∃ rₑ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ n : ℝ, N ≤ n →
      ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
      ∃ (z : t → Fin 3 → Fin 3 → ℂ) (U : t → Fin 3 → NormalWaveSpace → ℂ),
        (∀ i ℓ, tsupport (U i ℓ) ⊆ O) ∧
        (t.card : ℝ) ≤ Q*n^3 ∧
        (∀ y ∈ K, ∃ i : t, n*‖y-(p i).1.1‖ ≤ 1) ∧
        (∀ i ℓ, (∑ j, z i ℓ j*z i ℓ j = -1) ∧
          ‖phaseRealVector (z i ℓ)-gradient (normalWaveProfile g φ (p i)) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
        (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
          U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-(p i).1.1‖^2) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U i ℓ) w +
              (n : ℂ)*((n : ℂ)+2)*U i ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        (∀ i ℓ (r : ℝ), 0 ≤ r → r < rₑ → (Real.sqrt n)⁻¹ ≤ r →
          ∀ x y : NormalWaveSpace, ‖x-(p i).1.1‖ ≤ r → ‖y-(p i).1.1‖ ≤ r → n*‖y-x‖ ≤ 1 →
          ‖U i ℓ y-(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector (p i) (z i ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U i ℓ x‖ ≤
          (M*r)*‖(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector (p i) (z i ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U i ℓ x‖) ∧
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ y ∈ normalWaveEquiv.symm '' K,
        ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*φ (normalWaveEquiv y)) →
        let W := Real.exp (n*φ (normalWaveEquiv y))+R
        ∀ r : ℝ, 0 ≤ r →
        (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {γ | ‖realWaveJet n W (finiteWaveSuperposition (w ∘ normalWaveEquiv)
            (fun i ℓ => U i ℓ ∘ normalWaveEquiv) γ) y‖ ≤ r} ≤
          ENNReal.ofReal (C*n^28*r^4) := by
  classical
  obtain ⟨ρ,hρ,hfamily⟩ := actual_metric_superposition_complete_supported g φ hφ hK hO hKO hnc hcrit m D
  obtain ⟨ζ,hζ,hζc,hζs,hζ0⟩ := exists_smooth_complex_cutoff ρ hρ
  obtain ⟨T,hT,c,hc,M,hM,C,hC,r₀,hr₀,rₑ,hrₑ,N,hN,hdata⟩ := hfamily ζ hζ hζc hζs hζ0
  obtain ⟨Q,hQ,hnet⟩ := metric_center_polynomial_net_with_coverage g hK r₀ hr₀
  refine ⟨T,hT,c,hc,M,hM,C,hC,Q,hQ,rₑ,hrₑ,N,hN,?_⟩
  intro n hn
  obtain ⟨z,U,hSupport,hz,hU,hend,hlaw⟩ := hdata n hn
  obtain ⟨t,p,ht,hcover⟩ := hnet n (hN.trans hn)
  refine ⟨t,p,(fun i ℓ => z (p i) ℓ),(fun i ℓ => U (p i) ℓ),(fun i ℓ => hSupport (p i) ℓ),ht,?_,
    (fun i ℓ => hz (p i) ℓ),(fun i ℓ => hU (p i) ℓ),(fun i ℓ => hend (p i) ℓ),?_⟩
  · intro y hy
    obtain ⟨i,x,hxr,hxn,hxy,hnear⟩ := hcover (normalWaveEquiv.symm y) ⟨y,hy,rfl⟩
    exact ⟨i,by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hnear⟩
  intro w hw y hy R hR0 hR
  dsimp only
  intro r hr
  obtain ⟨i,x,hxr,hxn,hxy,hnear⟩ := hcover y hy
  have h := hlaw t p w hw i x hxr hxn
  dsimp only at h
  rw [hxy] at h
  exact h R hR0 hR r hr

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactActualWavesSignJets
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
lemma gaussian_pi_uncurry_preserving (I J : Type*) [Fintype I] [Fintype J] :
    MeasurePreserving (fun γ : I → J → ℂ => fun p : I×J => γ p.1 p.2)
      (Measure.pi (fun _ : I => Measure.pi (fun _ : J => stdGaussian ℂ)))
      (Measure.pi (fun _ : I×J => stdGaussian ℂ)) := by
  refine ⟨Measurable.of_eval (fun pair =>
    (measurable_pi_apply pair.2).comp (measurable_pi_apply pair.1)),?_⟩
  have h := Measure.infinitePi_map_curry_symm (fun (_ : I) (_ : J) => stdGaussian ℂ)
  simp only [Measure.infinitePi_eq_pi, MeasurableEquiv.coe_curry_symm] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

lemma gaussian_flat_sign_eq {I : Type*} [Fintype I]
    (U : I → Fin 3 → ℂ) (V : I → Fin 3 → ℂ) (a b : ℝ) :
    (Measure.pi (fun _ : I×Fin 3 => stdGaussian ℂ))
      {γ | (a+complexGaussianRealValue (fun k => U k.1 k.2) γ)*
        (b+complexGaussianRealValue (fun k => V k.1 k.2) γ)<0} =
    (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
      {γ | (a+∑ i, ∑ ℓ, (γ i ℓ*U i ℓ).re)*(b+∑ i, ∑ ℓ, (γ i ℓ*V i ℓ).re)<0} := by
  classical
  have hm (Z : I×Fin 3 → ℂ) : Measurable (complexGaussianRealValue Z) := by
    unfold complexGaussianRealValue
    exact Finset.measurable_sum _ (fun i _ => Complex.measurable_re.comp ((measurable_pi_apply i).mul_const _))
  have hs : MeasurableSet {γ : I×Fin 3 → ℂ |
      (a+complexGaussianRealValue (fun k => U k.1 k.2) γ)*
        (b+complexGaussianRealValue (fun k => V k.1 k.2) γ)<0} :=
    measurableSet_lt ((measurable_const.add (hm _)).mul (measurable_const.add (hm _))) measurable_const
  rw [←(gaussian_pi_uncurry_preserving I (Fin 3)).measure_preimage hs.nullMeasurableSet]
  congr 1
  ext γ
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,complexGaussianRealValue,Fintype.sum_prod_type]
end



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem compact_actual_waves_sign_and_jets_supported_oai
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∃ c₀ > 0, ∃ T > 0, ∃ c > 0, ∃ C > 0, ∃ Q > 0,
    ∃ N : ℝ, 2 ≤ N ∧ ∀ s : ℝ, N ≤ s →
    let n := s^4
    ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
    ∃ U : t → Fin 3 → NormalWaveSpace → ℂ,
      (∀ i ℓ, tsupport (U i ℓ) ⊆ O) ∧
      (t.card : ℝ) ≤ Q*n^3 ∧
      (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
        U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
        ∀ y : NormalWaveSpace, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-(p i).1.1‖^2) ∧
          ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U i ℓ) w +
            (n : ℂ)*((n : ℂ)+2)*U i ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
      (∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ y ∈ normalWaveEquiv.symm '' K,
        ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*φ (normalWaveEquiv y)) →
        let W := Real.exp (n*φ (normalWaveEquiv y))+R
        ∀ r : ℝ, 0 ≤ r →
        (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {γ | ‖realWaveJet n W (finiteWaveSuperposition (w ∘ normalWaveEquiv)
            (fun i ℓ => U i ℓ ∘ normalWaveEquiv) γ) y‖ ≤ r} ≤
          ENNReal.ofReal (C*n^28*r^4)) ∧
      ∀ b : NormalWaveSpace → ℝ, (∀ y ∈ K, |b y| ≤ c₀*Real.exp (n*φ y)) →
      ∀ x ∈ K, ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
      (∀ j, packetAxisShift x n ε ℓ j ∈ K) →
      ∃ j, ENNReal.ofReal p₀ ≤ (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {γ | finiteWaveSuperposition b U γ x *
          finiteWaveSuperposition b U γ (packetAxisShift x n ε ℓ j) < 0} := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hsign⟩ := compact_metric_packet_sign_gain g hK
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D
  obtain ⟨c₀,hc₀,hsg⟩ := hsign φ hφ
  obtain ⟨T,hT,c,hc,M,hM,C,hC,Q,hQ,rₑ,hrₑ,N₁,hN₁,hpack⟩ :=
    compact_actual_metric_packets_supported g φ hφ hK hO hKO hnc hcrit m D
  obtain ⟨N₂,hN₂,hsgn⟩ := hsg T c M rₑ (3*Q) hT hc hM hrₑ (by positivity)
  refine ⟨c₀,hc₀,T,hT,c,hc,C,hC,Q,hQ,max 2 (max N₁ N₂),le_max_left _ _,?_⟩
  intro s hs
  have hs2 : 2 ≤ s := (le_max_left _ _).trans hs
  have hsN₁ : N₁ ≤ s := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hs
  have hsN₂ : N₂ ≤ s := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hs
  have hs1 : 1 ≤ s := by linarith
  have hs4 : s ≤ s^4 := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (by norm_num : 1 ≤ (4:ℕ))
  dsimp only
  obtain ⟨t,p,z,U,hSupport,ht,hcover,hz,hU,hend,hjets⟩ := hpack (s^4) (hsN₁.trans hs4)
  refine ⟨t,p,U,hSupport,ht,hU,hjets,?_⟩
  intro b hb x hx ℓ hℓ hℓ' hy
  have hcard : (Fintype.card (t×Fin 3) : ℝ) ≤ (3*Q)*(s^4)^3 := by
    simp only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith [ht]
  obtain ⟨j,hj⟩ := hsgn s hsN₂ (t×Fin 3) (fun i => (p i.1).1)
    (fun i => z i.1 i.2) (fun i => U i.1 i.2) b hcard
    (fun i => (p i.1).property) (fun i => hz i.1 i.2) (by
      intro y hy
      obtain ⟨i,hi⟩ := hcover y hy
      exact ⟨(i,0),hi⟩)
    (fun i => (hU i.1 i.2).2.2.1) (by
      intro i y
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one]
        using ((hU i.1 i.2).2.2.2 y 0 (Nat.zero_le _)).1)
    (fun i => hend i.1 i.2) hb x hx ℓ hℓ hℓ' hy
  refine ⟨j,?_⟩
  rw [gaussian_flat_sign_eq (fun i ℓ => U i ℓ x)
    (fun i k => U i k (packetAxisShift x (s^4) ε ℓ j)) (b x)
    (b (packetAxisShift x (s^4) ε ℓ j))] at hj
  exact hj

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.compact_actual_waves_sign_and_jets_supported_oai := @OAI.YauCounterexamples.compact_actual_waves_sign_and_jets_supported_oai
