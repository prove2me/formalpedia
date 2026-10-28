-- Prove2me | solution 1 for OAI.YauCounterexamples.compact_packet_angular_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:05:30.339434+00:00
-- url     : https://prove2.me/submissions/04905a88-f01c-4e99-9ff3-c218f30f701f

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_HessianJet
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma compact_uniform_value_radius {X B : Type*} [TopologicalSpace X]
    [NormedAddCommGroup B] (H : X × E → B) (hH : Continuous H)
    {P : Set X} (hP : IsCompact P) {c : ℝ} (hc : 0 < c) :
    ∃ r > 0, ∀ p ∈ P, ∀ y ∈ Metric.ball (0 : E) r,
      ‖H (p,y) - H (p,0)‖ < c := by
  have hH0 : Continuous (fun q : X × E => H (q.1,0)) :=
    hH.comp (continuous_fst.prodMk continuous_const)
  have hopen : IsOpen {q : X × E | ‖H q - H (q.1,0)‖ < c} :=
    isOpen_lt (hH.sub hH0).norm continuous_const
  have hsub : P ×ˢ {(0 : E)} ⊆ {q : X × E | ‖H q - H (q.1,0)‖ < c} := by
    rintro ⟨p,y⟩ ⟨hp,hy⟩
    have hy0 : y = 0 := mem_singleton_iff.mp hy
    subst y
    change ‖H (p,0) - H (p,0)‖ < c
    simpa only [sub_self, norm_zero] using hc
  obtain ⟨u,v,hu,hv,hPu,h0v,huv⟩ := generalized_tube_lemma hP
    isCompact_singleton hopen hsub
  obtain ⟨r,hr,hrv⟩ := Metric.isOpen_iff.mp hv 0 (h0v (mem_singleton 0))
  exact ⟨r,hr,fun p hp y hy => huv ⟨hPu hp,hrv hy⟩⟩

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
open Set Filter MvPolynomial
open scoped Topology ContDiff



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

lemma compact_selfMetricFlat_lower (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v : E, m*‖v‖^2 ≤ selfMetricFlat g x v v :=
  compact_positive_bilinear_lower hK (selfMetricFlat g) (contDiff_selfMetricFlat g).continuous
    (fun x _ _ hv => selfMetricFlat_pos g x hv)


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
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
local instance normalTriNorm_r5810a3_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
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

local instance frameDualNorm_r5810a3_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.YauCounterexamples.frameDualSpace
local instance frameFormNorm_r5810a3_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance frameFormSpace_r5810a3_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma metricFrameSet_isClosed (g : SmoothMetric E E) {K : Set E} (hK : IsClosed K) :
    IsClosed (metricFrameSet g K) := by
  apply (hK.preimage continuous_fst).inter
  change IsClosed {q : E × (E →L[ℝ] E) | ∀ v w : E,
    selfMetricFlat g q.1 (q.2 v) (q.2 w) = inner ℝ v w}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro w
  exact isClosed_eq
    (((contDiff_selfMetricFlat g).continuous.comp continuous_fst).clm_apply
      (continuous_snd.clm_apply continuous_const) |>.clm_apply
      (continuous_snd.clm_apply continuous_const)) continuous_const

lemma metricFrameSet_bound (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ R > 0, ∀ q ∈ metricFrameSet g K, ‖q.2‖ ≤ R := by
  obtain ⟨m,hm,hml⟩ := compact_selfMetricFlat_lower g hK
  refine ⟨(Real.sqrt m)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hm), ?_⟩
  intro q hq
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  intro v
  have hlow := hml q.1 hq.1 (q.2 v)
  rw [hq.2 v v, real_inner_self_eq_norm_sq] at hlow
  have hh : Real.sqrt m * ‖q.2 v‖ ≤ ‖v‖ :=
    le_of_sq_le_sq (by simpa only [mul_pow,Real.sq_sqrt hm.le] using hlow) (norm_nonneg _)
  rw [← div_eq_inv_mul, le_div_iff₀ (Real.sqrt_pos.mpr hm)]
  rwa [mul_comm]

theorem metricFrameSet_isCompact (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    IsCompact (metricFrameSet g K) := by
  obtain ⟨R,hR,hb⟩ := metricFrameSet_bound g hK
  apply (hK.prod (isCompact_closedBall (0 : E →L[ℝ] E) R)).of_isClosed_subset
    (metricFrameSet_isClosed g hK.isClosed)
  intro q hq
  exact ⟨hq.1, by simpa only [Metric.mem_closedBall, dist_zero_right] using hb q hq⟩

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

lemma metricFrameSet_inverse_continuousOn (g : SmoothMetric E E) {K : Set E} :
    ContinuousOn (fun q : E × (E →L[ℝ] E) => q.2.inverse) (metricFrameSet g K) := by
  intro q hq
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  have h : q.2.IsInvertible := ⟨A,hA⟩
  exact (h.contDiffAt_map_inverse (n := (∞ : WithTop ℕ∞))).continuousAt.comp
    continuous_snd.continuousAt |>.continuousWithinAt

lemma metricFrameSet_inverse_bound (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ R > 0, ∀ q ∈ metricFrameSet g K, ‖q.2.inverse‖ ≤ R := by
  obtain ⟨R,hR⟩ := (metricFrameSet_isCompact g hK).exists_bound_of_continuousOn
    (metricFrameSet_inverse_continuousOn g)
  refine ⟨max 1 R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q hq
  exact (hR q hq).trans (le_max_right _ _)
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FrameInverseApply
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma normalPhaseCovector_apply (q : NormalWaveParameter) (z : Fin 3 → ℂ) (v : NormalWaveSpace) :
    normalPhaseCovector q z v = ∑ i, ((normalWaveEquiv.symm (q.2.inverse v)) i : ℂ)*z i := by
  simp [normalPhaseCovector,Complex.real_smul]

end



open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_PhaseImagVector
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

lemma normalImagCovector_apply (q : NormalWaveParameter) (z : Fin 3 → ℂ) (v : NormalWaveSpace) :
    normalImagCovector q z v = inner ℝ (phaseImagVector z) (q.2.inverse v) := by
  change (normalPhaseCovector q z v).im = _
  rw [normalPhaseCovector_apply]
  simp only [Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
    phaseImagVector,Pi.star_apply,star_trivial]
  rfl

lemma null_phase_imag_energy {z : Fin 3 → ℂ} (hz : ∑ i, z i*z i = -1) :
    ‖phaseImagVector z‖^2 = 1+‖phaseRealVector z‖^2 := by
  have h := congrArg Complex.re hz
  simp only [Complex.re_sum,Complex.mul_re,Complex.neg_re,Complex.one_re,
    Finset.sum_sub_distrib] at h
  simp only [←pow_two] at h
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  change (∑ i, ((z i).im)^2) = 1+∑ i, ((z i).re)^2
  linarith

lemma normalImagCovector_comp_frame (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K)
    (z : Fin 3 → ℂ) :
    (normalImagCovector q z).comp q.2 = InnerProductSpace.toDual ℝ PhaseSpace (phaseImagVector z) := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  ext v
  simp only [ContinuousLinearMap.comp_apply,normalImagCovector_apply,←hA,
    ContinuousLinearMap.inverse_equiv,ContinuousLinearEquiv.coe_coe,
    A.symm_apply_apply,InnerProductSpace.toDual_apply_apply]

lemma normalImagCovector_eq (q : NormalWaveParameter) (z : Fin 3 → ℂ) :
    normalImagCovector q z =
      (InnerProductSpace.toDual ℝ PhaseSpace (phaseImagVector z)).comp q.2.inverse := by
  ext v
  exact normalImagCovector_apply q z v

lemma euclidean_covector_squared_norm (β : PhaseSpace →L[ℝ] ℝ) :
    ‖β‖^2 = ∑ i : Fin 3, (β (EuclideanSpace.basisFun (Fin 3) ℝ i))^2 := by
  let v := (InnerProductSpace.toDual ℝ PhaseSpace).symm β
  have hv : ‖v‖ = ‖β‖ := (InnerProductSpace.toDual ℝ PhaseSpace).symm.norm_map β
  rw [←hv,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  have hi : v i = β (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
    rw [←EuclideanSpace.inner_basisFun_real]
    exact InnerProductSpace.toDual_symm_apply
  rw [hi]

theorem compact_normal_angular_energy (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ c > 0, ∃ C > 0, ∀ q ∈ metricFrameSet g K, ∀ z : Fin 3 → ℂ,
      (∑ i, z i*z i = -1) →
      c*(1+‖phaseRealVector z‖^2) ≤
        ∑ i : Fin 3, (normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i))^2 ∧
      (∑ i : Fin 3, (normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i))^2) ≤
        C*(1+‖phaseRealVector z‖^2) := by
  obtain ⟨R,hR,hb⟩ := metricFrameSet_bound g hK
  obtain ⟨S,hS,hi⟩ := metricFrameSet_inverse_bound g hK
  refine ⟨(R^2)⁻¹,inv_pos.mpr (sq_pos_of_pos hR),S^2,sq_pos_of_pos hS,?_⟩
  intro q hq z hz
  have hlo : ‖phaseImagVector z‖ ≤ ‖normalImagCovector q z‖*R := by
    have hh := ContinuousLinearMap.opNorm_comp_le (normalImagCovector q z) q.2
    rw [normalImagCovector_comp_frame g hq z,LinearIsometryEquiv.norm_map] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hb q hq) (norm_nonneg _))
  have hhi : ‖normalImagCovector q z‖ ≤ S*‖phaseImagVector z‖ := by
    rw [normalImagCovector_eq]
    have hh := ContinuousLinearMap.opNorm_comp_le
      (InnerProductSpace.toDual ℝ PhaseSpace (phaseImagVector z)) q.2.inverse
    rw [LinearIsometryEquiv.norm_map] at hh
    exact hh.trans (by nlinarith [hi q hq,norm_nonneg (phaseImagVector z)])
  rw [←euclidean_covector_squared_norm,←null_phase_imag_energy hz]
  constructor
  · have hs : ‖phaseImagVector z‖^2 ≤ ‖normalImagCovector q z‖^2*R^2 := by
      nlinarith [sq_nonneg (‖normalImagCovector q z‖*R-‖phaseImagVector z‖),
        norm_nonneg (phaseImagVector z),norm_nonneg (normalImagCovector q z)]
    calc
      _ ≤ (R^2)⁻¹*(‖normalImagCovector q z‖^2*R^2) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (sq_nonneg R))
      _ = _ := by field_simp
  · nlinarith [sq_nonneg (S*‖phaseImagVector z‖-‖normalImagCovector q z‖),
      norm_nonneg (phaseImagVector z),norm_nonneg (normalImagCovector q z)]
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ProfileFrequencyEnergy
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

lemma profileFrequencyEnergy_ge_one (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) :
    1 ≤ profileFrequencyEnergy g φ x := by
  unfold profileFrequencyEnergy
  by_cases h : coordinateMetricGradient g φ x = 0
  · simp [h]
  · linarith [selfMetricFlat_pos g x h]

lemma profileFrequencyScale_sq (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) :
    profileFrequencyScale g φ x ^ 2 = profileFrequencyEnergy g φ x :=
  Real.sq_sqrt (zero_le_one.trans (profileFrequencyEnergy_ge_one g φ x))

lemma profileFrequencyScale_ge_one (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) :
    1 ≤ profileFrequencyScale g φ x := by
  have h := Real.sqrt_nonneg (profileFrequencyEnergy g φ x)
  have he := profileFrequencyScale_sq g φ x
  have h1 := profileFrequencyEnergy_ge_one g φ x
  change 0 ≤ profileFrequencyScale g φ x at h
  nlinarith

lemma continuous_profileFrequencyEnergy (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (profileFrequencyEnergy g φ) := by
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x
      (contDiff_selfMetricFlat g).contDiffAt
  have hg : Continuous (coordinateMetricGradient g φ) :=
    (hGi.clm_apply (hφ.fderiv_right (m := ∞) (by simp))).continuous
  exact continuous_const.add (((contDiff_selfMetricFlat g).continuous.clm_apply hg).clm_apply hg)

lemma profileFrequencyEnergy_frame (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K) :
    profileFrequencyEnergy g φ q.1 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 := by
  unfold profileFrequencyEnergy
  rw [←metric_frame_gradient g hφ hq,hq.2,real_inner_self_eq_norm_sq]

lemma nearby_characteristic_energy (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ z : Fin 3 → ℂ, ∀ x : NormalWaveSpace,
      ‖x-q.1‖ ≤ r → ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ r →
      profileFrequencyEnergy g φ x/2 ≤ 1+‖phaseRealVector z‖^2 ∧
      1+‖phaseRealVector z‖^2 ≤ 2*profileFrequencyEnergy g φ x := by
  have hE := continuous_profileFrequencyEnergy g hφ
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hE.continuousOn
  let M := max 1 (C+1)
  have hM : 1 ≤ M := le_max_left _ _
  have hCM : C ≤ M := le_trans (by linarith) (le_max_right 1 (C+1))
  let H := fun w : NormalWaveSpace × NormalWaveSpace => profileFrequencyEnergy g φ (w.1+w.2)
  obtain ⟨rv,hrv,hvar⟩ := compact_uniform_value_radius H (hE.comp (continuous_fst.add continuous_snd))
    hK (show (0 : ℝ) < 1/4 by norm_num)
  let r := min (rv/2) (min 1 (1/(4*(2*M+1))))
  have hr : 0 < r := lt_min (half_pos hrv) (lt_min zero_lt_one (by positivity))
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrrv : r < rv := (min_le_left _ _).trans_lt (by linarith)
  have hrM : (2*M+1)*r ≤ 1/4 := by
    have hh := (min_le_right (rv/2) _).trans (min_le_right 1 (1/(4*(2*M+1))))
    have he := (le_div_iff₀ (show 0 < 4*(2*M+1) by positivity)).mp hh
    nlinarith
  refine ⟨r,hr,?_⟩
  intro q hq z x hx hz
  let a := gradient (normalWaveProfile g φ q) 0
  have ha : ‖a‖ ≤ M := by
    have he := profileFrequencyEnergy_frame g hφ hq
    have hb := (le_abs_self (profileFrequencyEnergy g φ q.1)).trans (hC q.1 hq.1)
    change profileFrequencyEnergy g φ q.1 = 1+‖a‖^2 at he
    nlinarith [sq_nonneg (M-1),norm_nonneg a]
  have hbda : |‖phaseRealVector z‖-‖a‖| ≤ r := (abs_norm_sub_norm_le _ _).trans hz
  have hb : ‖phaseRealVector z‖ ≤ M+1 := by
    have ht := (abs_le.mp hbda).2
    linarith
  have hs : |‖phaseRealVector z‖^2-‖a‖^2| ≤ 1/4 := by
    calc
      _ = |‖phaseRealVector z‖-‖a‖| *(‖phaseRealVector z‖+‖a‖) := by
        rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        ring
      _ ≤ r*(2*M+1) := mul_le_mul hbda (by linarith)
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) hr.le
      _ ≤ 1/4 := by nlinarith [hrM]
  have hv : |profileFrequencyEnergy g φ x-profileFrequencyEnergy g φ q.1| < 1/4 := by
    have hh := hvar q.1 hq.1 (x-q.1)
      (show x-q.1 ∈ Metric.ball 0 rv by simpa only [Metric.mem_ball,dist_zero_right] using hx.trans_lt hrrv)
    simpa only [H,add_sub_cancel,add_zero,Real.norm_eq_abs] using hh
  have he := profileFrequencyEnergy_frame g hφ hq
  have h1 := profileFrequencyEnergy_ge_one g φ x
  change profileFrequencyEnergy g φ q.1 = 1+‖a‖^2 at he
  obtain ⟨hs₁,hs₂⟩ := abs_le.mp hs
  obtain ⟨hv₁,hv₂⟩ := abs_lt.mp hv
  constructor <;> linarith

theorem compact_normal_profile_angular_energy (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ c > 0, ∃ C > 0, ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
      ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ z : Fin 3 → ℂ, ∀ x : NormalWaveSpace,
        (∑ i, z i*z i = -1) → ‖x-q.1‖ ≤ r →
        ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ r →
        c*profileFrequencyScale g φ x^2 ≤
          ∑ i : Fin 3, (normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i))^2 ∧
        (∑ i : Fin 3, (normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i))^2) ≤
          C*profileFrequencyScale g φ x^2 := by
  obtain ⟨c,hc,C,hC,hb⟩ := compact_normal_angular_energy g hK
  refine ⟨c/2,half_pos hc,2*C,by positivity,?_⟩
  intro φ hφ
  obtain ⟨r,hr,he⟩ := nearby_characteristic_energy g hφ hK
  refine ⟨r,hr,?_⟩
  intro q hq z x hz hx hlin
  obtain ⟨hlo,hhi⟩ := he q hq z x hx hlin
  obtain ⟨hlo',hhi'⟩ := hb q hq z hz
  rw [profileFrequencyScale_sq]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo hc.le]
  · nlinarith [mul_le_mul_of_nonneg_left hhi hC.le]
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ScaledThreeAxisEnergy
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

lemma scaled_three_axis_energy {L ℓ ε c C : ℝ} (hL : 0 < L) (hℓ : L ≤ ℓ)
    (hℓ' : ℓ ≤ 2*L) (hε : 0 ≤ ε) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hsmall : ε^2*C ≤ 1) (β : Fin 3 → ℝ)
    (hlo : c*L^2 ≤ ∑ i, (β i)^2) (hhi : (∑ i, (β i)^2) ≤ C*L^2) :
    (∀ i, |ε/ℓ*β i| ≤ 1) ∧ c*ε^2/4 ≤ ∑ i, (ε/ℓ*β i)^2 := by
  have hpos : 0 < ℓ := hL.trans_le hℓ
  have hrlo : (1/2 : ℝ) ≤ L/ℓ := (le_div_iff₀ hpos).mpr (by linarith)
  have hrhi : L/ℓ ≤ 1 := (div_le_iff₀ hpos).mpr (by simpa using hℓ)
  have hrrlo : (1/4 : ℝ) ≤ (L/ℓ)^2 := by nlinarith
  have hrrhi : (L/ℓ)^2 ≤ 1 := by nlinarith
  have heq : (∑ i, (ε/ℓ*β i)^2) = (ε/ℓ)^2*(∑ i, (β i)^2) := by
    simp only [mul_pow,Finset.mul_sum]
  have hlo' : c*ε^2/4 ≤ ∑ i, (ε/ℓ*β i)^2 := by
    rw [heq]
    calc
      _ ≤ c*ε^2*(L/ℓ)^2 := by
        have hmul := mul_le_mul_of_nonneg_left hrrlo (mul_nonneg hc (pow_nonneg hε 2))
        nlinarith
      _ = (ε/ℓ)^2*(c*L^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (sq_nonneg _)
  have hhi' : (∑ i, (ε/ℓ*β i)^2) ≤ 1 := by
    rw [heq]
    calc
      _ ≤ (ε/ℓ)^2*(C*L^2) := mul_le_mul_of_nonneg_left hhi (sq_nonneg _)
      _ = (ε^2*C)*(L/ℓ)^2 := by ring
      _ ≤ ε^2*C := mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) hC) hrrhi
      _ ≤ 1 := hsmall
  refine ⟨?_,hlo'⟩
  intro i
  have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
    (f := fun j => (ε/ℓ*β j)^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hi : (ε/ℓ*β i)^2 ≤ 1 := hs.trans hhi'
  rw [abs_le]
  constructor <;> nlinarith

theorem compact_packet_angular_gap_oai (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ κ > 0, κ ≤ 1 ∧
      ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
      ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ z : Fin 3 → ℂ, ∀ x : NormalWaveSpace,
        (∑ i, z i*z i = -1) → ‖x-q.1‖ ≤ r →
        ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ r →
        ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
        let θ := fun i => ε/ℓ*normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (∀ i, |θ i| ≤ 1) ∧ κ ≤ ∑ i, (θ i)^2 := by
  obtain ⟨c,hc,C,hC,hb⟩ := compact_normal_profile_angular_energy g hK
  let ε := 1/(C+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := (div_le_iff₀ (by linarith : 0 < C+1)).mpr (by linarith)
  have hεC : ε^2*C ≤ 1 := by
    have he : ε*(C+1) = 1 := by dsimp [ε]; field_simp
    have hsq := sq_nonneg (ε*C)
    nlinarith [mul_nonneg hε.le hC.le]
  let κ := min 1 (c*ε^2/4)
  have hκ : 0 < κ := lt_min zero_lt_one (by positivity)
  refine ⟨ε,hε,hε1,κ,hκ,min_le_left _ _,?_⟩
  intro φ hφ
  obtain ⟨r,hr,he⟩ := hb φ hφ
  refine ⟨r,hr,?_⟩
  intro q hq z x hz hx hlin ℓ hℓ hℓ'
  obtain ⟨hlo,hhi⟩ := he q hq z x hz hx hlin
  have hh := scaled_three_axis_energy (lt_of_lt_of_le zero_lt_one (profileFrequencyScale_ge_one g φ x))
    hℓ hℓ' hε.le hc.le hC.le hεC
    (fun i => normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i)) hlo hhi
  exact ⟨hh.1,(min_le_right _ _).trans hh.2⟩
end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.compact_packet_angular_gap_oai := @OAI.YauCounterexamples.compact_packet_angular_gap_oai
