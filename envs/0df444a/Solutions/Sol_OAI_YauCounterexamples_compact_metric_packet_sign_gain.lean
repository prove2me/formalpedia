-- Prove2me | solution 1 for OAI.YauCounterexamples.compact_metric_packet_sign_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:04:43.306988+00:00
-- url     : https://prove2.me/submissions/48a142c9-8ebd-4d67-83a8-5c9a76d0b69e

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_compact_packet_angular_gap
import Theorems.Thm_OAI_YauCounterexamples_localized_packet_sign_probability

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

lemma exists_metric_orthonormal_frame (g : SmoothMetric E E) (p : E) :
    ∃ A : E ≃L[ℝ] E, ∀ v w, selfMetricFlat g p (A v) (A w) = inner ℝ v w := by
  let : RiemannianBundle (fun x : E => TangentSpace 𝓘(ℝ,E) x) :=
    ⟨g.toRiemannianMetric⟩
  let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) p
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) p) :=
    Module.Finite.equiv j.symm.toLinearEquiv
  let e : E ≃ₗᵢ[ℝ] TangentSpace 𝓘(ℝ,E) p :=
    (stdOrthonormalBasis ℝ E).equiv
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ,E) p))
      (finCongr j.toLinearEquiv.finrank_eq.symm)
  refine ⟨e.toContinuousLinearEquiv.trans j, ?_⟩
  intro v w
  have h := e.inner_map_map v w
  change g.inner p (e v) (e w) = inner ℝ v w at h
  simpa only [selfMetricFlat, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    j] using h

attribute [local instance] OAI.YauCounterexamples.normalDualNorm
attribute [local instance] OAI.YauCounterexamples.normalFormNorm
attribute [local instance] OAI.YauCounterexamples.normalDualSpace
attribute [local instance] OAI.YauCounterexamples.normalFormSpace
local instance normalTriNorm_reb9fce_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
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

lemma metricFrameSet_fiber_nonempty (g : SmoothMetric E E) {K : Set E} {p : E}
    (hp : p ∈ K) : ∃ A : E →L[ℝ] E, (p,A) ∈ metricFrameSet g K := by
  obtain ⟨A,hA⟩ := exists_metric_orthonormal_frame g p
  exact ⟨A, hp, hA⟩

local instance frameDualNorm_reb9fce_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.YauCounterexamples.frameDualSpace
local instance frameFormNorm_reb9fce_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance frameFormSpace_reb9fce_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PolynomialGaussianTailTendsto
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

lemma polynomial_gaussian_tail_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => t^12*Real.exp (-a*t^2)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 6 a ha).comp
    (tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num) : Tendsto (fun t : ℝ => t^2) atTop atTop)
  simpa [Function.comp_def,Real.rpow_natCast,←pow_mul] using h

lemma quartic_inverse_bounds {t : ℝ} (ht : 1 ≤ t) :
    0 < t ∧ 1 ≤ t^4 ∧ (t^4)⁻¹ ≤ t⁻¹ ∧ (Real.sqrt (t^4))⁻¹ ≤ 2/t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hs : Real.sqrt (t^4) = t^2 := by
    rw [show t^4 = (t^2)^2 by ring,Real.sqrt_sq (sq_nonneg t)]
  have h4 : 1 ≤ t^4 := one_le_pow₀ ht
  have h14 : (t^4)⁻¹ ≤ t⁻¹ := inv_anti₀ ht0 (le_self_pow₀ ht (by norm_num : (4 : ℕ) ≠ 0))
  have h12 : (t^2)⁻¹ ≤ t⁻¹ := inv_anti₀ ht0 (le_self_pow₀ ht (by norm_num : (2 : ℕ) ≠ 0))
  refine ⟨ht0,h4,h14,?_⟩
  rw [hs]
  exact h12.trans (by rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr ht0])

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PacketAxisShift
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

lemma quartic_tail_budget_eventually {a B δ c : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, B*(t^12*Real.exp (-a*t^2)) ≤ δ*c := by
  have ht := (tendsto_const_nhds (x := B) (f := atTop)).mul (polynomial_gaussian_tail_tendsto ha)
  have ht' : Tendsto (fun t : ℝ => B*(t^12*Real.exp (-a*t^2))) atTop (𝓝 0) := by simpa using ht
  filter_upwards [ht'.eventually_lt_const (mul_pos hδ hc)] with t ht using ht.le
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FrameInverseApply
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples



open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

lemma frame_inverse_apply (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K)
    (v : NormalWaveSpace) : q.2 (q.2.inverse v) = v := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  rw [←hA,ContinuousLinearMap.inverse_equiv]
  exact A.apply_symm_apply v

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

lemma profileFrequencyEnergy_frame (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K) :
    profileFrequencyEnergy g φ q.1 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 := by
  unfold profileFrequencyEnergy
  rw [←metric_frame_gradient g hφ hq,hq.2,real_inner_self_eq_norm_sq]

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactProfileUnitLipschitz
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
open scoped Topology ContDiff RealInnerProductSpace

theorem compact_profile_slope_bound (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ H > 0, ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
      ∀ x ∈ K, ‖fderiv ℝ φ x‖ ≤ H*profileFrequencyScale g φ x := by
  obtain ⟨S,hS,hbound⟩ := metricFrameSet_inverse_bound g hK
  refine ⟨S,hS,?_⟩
  intro φ hφ x hx
  obtain ⟨F,hF⟩ := metricFrameSet_fiber_nonempty g hx
  let q : NormalWaveParameter := (x,F)
  have hq : q ∈ metricFrameSet g K := hF
  let a := gradient (normalWaveProfile g φ q) 0
  have ha : ‖a‖ ≤ profileFrequencyScale g φ x := by
    have he := profileFrequencyEnergy_frame g hφ hq
    have hs := profileFrequencyScale_sq g φ x
    have hp := profileFrequencyScale_ge_one g φ x
    change profileFrequencyEnergy g φ x = 1+‖a‖^2 at he
    nlinarith [norm_nonneg a]
  have heq : fderiv ℝ φ x = (InnerProductSpace.toDual ℝ PhaseSpace a).comp q.2.inverse := by
    ext v
    change fderiv ℝ φ q.1 v = inner ℝ a (q.2.inverse v)
    rw [normalWaveProfile_gradient_pairing g hφ,frame_inverse_apply g hq]
  rw [heq]
  calc
    _ ≤ ‖InnerProductSpace.toDual ℝ PhaseSpace a‖*‖q.2.inverse‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖a‖*‖q.2.inverse‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ profileFrequencyScale g φ x*S :=
      mul_le_mul ha (hbound q hq) (norm_nonneg _) (by linarith [profileFrequencyScale_ge_one g φ x])
    _ = _ := by ring

lemma normalized_real_growth_bounds {L ℓ ε H : ℝ} (hL : 0 < L) (hℓ : L ≤ ℓ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hH : 0 ≤ H)
    (a : NormalWaveSpace →L[ℝ] ℝ) (ha : ‖a‖ ≤ H*L) (i : Fin 3) :
    Real.exp (-H) ≤ Real.exp ((ε/ℓ)*a (EuclideanSpace.basisFun (Fin 3) ℝ i)) ∧
    Real.exp ((ε/ℓ)*a (EuclideanSpace.basisFun (Fin 3) ℝ i)) ≤ Real.exp H := by
  have hℓ0 : 0 < ℓ := hL.trans_le hℓ
  have hi : |a (EuclideanSpace.basisFun (Fin 3) ℝ i)| ≤ H*L := by
    have hi' := a.le_opNorm (EuclideanSpace.basisFun (Fin 3) ℝ i)
    simpa using hi'.trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  have hεℓ : 0 ≤ ε/ℓ := div_nonneg hε hℓ0.le
  have hh : |(ε/ℓ)*a (EuclideanSpace.basisFun (Fin 3) ℝ i)| ≤ H := by
    rw [abs_mul,abs_of_nonneg hεℓ]
    calc
      _ ≤ ε/ℓ*(H*L) := mul_le_mul_of_nonneg_left hi hεℓ
      _ = H*ε*(L/ℓ) := by ring
      _ ≤ H*ε := mul_le_of_le_one_right (mul_nonneg hH hε) ((div_le_one hℓ0).mpr hℓ)
      _ ≤ H := mul_le_of_le_one_right hH hε1
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp hh).1,Real.exp_le_exp.mpr (abs_le.mp hh).2⟩

end



open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

lemma compact_profile_unit_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q ∈ K, ∀ x : E, ‖x-q‖ ≤ 1 →
      ‖fderiv ℝ φ x‖ ≤ C ∧ |φ x-φ q| ≤ C*‖x-q‖ := by
  let L := (fun p : E×E => p.1+p.2) '' (K ×ˢ Metric.closedBall 0 1)
  have hL : IsCompact L := (hK.prod (isCompact_closedBall 0 1)).image
    (continuous_fst.add continuous_snd)
  obtain ⟨C,hbound⟩ := hL.exists_bound_of_continuousOn
    (hφ.fderiv_right (m := ∞) (by simp)).continuous.continuousOn
  let H := max 1 C
  have hb (q) (hq : q ∈ K) (x) (hx : ‖x-q‖ ≤ 1) : ‖fderiv ℝ φ x‖ ≤ H := by
    apply (hbound x ?_).trans (le_max_right _ _)
    refine ⟨(q,x-q),⟨hq,?_⟩,add_sub_cancel q x⟩
    simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  refine ⟨H,le_max_left _ _,?_⟩
  intro q hq x hx
  refine ⟨hb q hq x hx,?_⟩
  have hh := (convex_closedBall q (1 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hφ.differentiable (by simp) y)
    (fun y hy => hb q hq y (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy))
    (Metric.mem_closedBall_self zero_le_one)
    (show x ∈ Metric.closedBall q 1 by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
  exact hh

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactMetricPacketSignGain
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace YauCounterexamples

theorem compact_metric_packet_sign_gain_oai
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ → ∃ c₀ > 0,
    ∀ T c M rₑ Q : ℝ, 0 < T → 0 < c → 0 < M → 0 < rₑ → 0 < Q →
    ∃ N : ℝ, 2 ≤ N ∧ ∀ t : ℝ, N ≤ t → ∀ (I : Type) [Fintype I] [DecidableEq I]
      (q : I → NormalWaveParameter) (z : I → Fin 3 → ℂ)
      (U : I → NormalWaveSpace → ℂ) (b : NormalWaveSpace → ℝ),
      (Fintype.card I : ℝ) ≤ Q*(t^4)^3 →
      (∀ i, q i ∈ metricFrameSet g K) →
      (∀ i, (∑ j, z i j*z i j = -1) ∧
        ‖phaseRealVector (z i)-gradient (normalWaveProfile g φ (q i)) 0‖ ≤ (Real.sqrt (t^4))⁻¹) →
      (∀ y ∈ K, ∃ i, t^4*‖y-(q i).1‖ ≤ 1) →
      (∀ i, U i (q i).1 = Complex.exp (((t^4 : ℝ) : ℂ)*(φ (q i).1 : ℂ))) →
      (∀ i y, ‖U i y‖ ≤ T*Real.exp (t^4*φ y)*Real.exp (-c*t^4*‖y-(q i).1‖^2)) →
      (∀ i (r : ℝ), 0 ≤ r → r < rₑ → (Real.sqrt (t^4))⁻¹ ≤ r →
        ∀ x y : NormalWaveSpace, ‖x-(q i).1‖ ≤ r → ‖y-(q i).1‖ ≤ r → t^4*‖y-x‖ ≤ 1 →
        ‖U i y-(Real.exp (t^4*fderiv ℝ φ x (y-x)) : ℂ)*
          Complex.exp (((t^4*normalImagCovector (q i) (z i) (y-x) : ℝ) : ℂ)*Complex.I)*U i x‖ ≤
        (M*r)*‖(Real.exp (t^4*fderiv ℝ φ x (y-x)) : ℂ)*
          Complex.exp (((t^4*normalImagCovector (q i) (z i) (y-x) : ℝ) : ℂ)*Complex.I)*U i x‖) →
      (∀ y ∈ K, |b y| ≤ c₀*Real.exp (t^4*φ y)) →
      ∀ x ∈ K, ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
      (∀ j, packetAxisShift x (t^4) ε ℓ j ∈ K) →
      ∃ j, ENNReal.ofReal p ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (b x+complexGaussianRealValue (fun i => U i x) γ)*
          (b (packetAxisShift x (t^4) ε ℓ j)+
            complexGaussianRealValue (fun i => U i (packetAxisShift x (t^4) ε ℓ j)) γ) < 0} := by
  obtain ⟨ε,hε,hε1,κ,hκ,hκ1,hgap⟩ := compact_packet_angular_gap g hK
  obtain ⟨Hs,hHs,hslope⟩ := compact_profile_slope_bound g hK
  obtain ⟨p,hp,hprob⟩ := localized_packet_sign_probability hκ hκ1
  refine ⟨ε,hε,hε1,p,hp,?_⟩
  intro φ hφ
  obtain ⟨rₐ,hrₐ,hang⟩ := hgap φ hφ
  obtain ⟨H,hH,hφbound⟩ := compact_profile_unit_lipschitz φ hφ hK
  let c₀ := Real.exp (-2*H)/2
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨c₀,hc₀,?_⟩
  intro T c M rₑ Q hT hc hM hrₑ hQ
  let δ := min (1/16) (κ/96)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1/16 := min_le_left _ _
  have hδκ : δ ≤ κ/96 := min_le_right _ _
  let r := min rₑ (min rₐ (δ/(2*(M+1))))
  have hr : 0 < r := lt_min hrₑ (lt_min hrₐ (by positivity))
  have htend : Tendsto (fun t : ℝ => 2/t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hevent := htend.eventually_lt_const hr
  have htail := quartic_tail_budget_eventually (B := Q*T*Real.exp H)
    (a := c/4) (δ := δ/2) (c := Real.exp (-Hs)*c₀) (by positivity) (half_pos hδ) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((eventually_ge_atTop (2 : ℝ)).and (hevent.and htail))
  refine ⟨max 2 N,le_max_left _ _,?_⟩
  intro t ht I _ _ q z U b hcount hq hz hcov hcenter hloc hend hb x hx ℓ hℓ hℓ' hy
  obtain ⟨ht2,htr,htail'⟩ := hN t ((le_max_right _ _).trans ht)
  have ht1 : 1 ≤ t := by linarith
  obtain ⟨ht0,hn1,hinv,hsqrt⟩ := quartic_inverse_bounds ht1
  have hrad : 0 ≤ 2/t := by positivity
  have htre : 2/t < rₑ := htr.trans_le (min_le_left _ _)
  have htra : 2/t ≤ rₐ := htr.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMr : M*(2/t) ≤ δ/2 := by
    have hh : 2/t ≤ δ/(2*(M+1)) := htr.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (show 0 < 2*(M+1) by positivity)).mp hh
    nlinarith
  have hinvra : t⁻¹ ≤ rₐ := le_trans (by rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr ht0]) htra
  have hbudget : (Fintype.card I : ℝ)*T*Real.exp H*Real.exp (-c*t^2/4) ≤
      (δ/2)*Real.exp (-Hs)*(Real.exp (-2*H)/2) := by
    have hh : (Fintype.card I : ℝ) ≤ Q*t^12 := by simpa only [←pow_mul] using hcount
    calc
      _ ≤ (Q*t^12)*T*Real.exp H*Real.exp (-c*t^2/4) := by gcongr
      _ = (Q*T*Real.exp H)*(t^12*Real.exp (-(c/4)*t^2)) := by
        rw [show -(c/4)*t^2 = -c*t^2/4 by ring]
        ring
      _ ≤ _ := by simpa only [c₀,mul_assoc] using htail'
  apply hprob I φ K (fun i => (q i).1) (fun i => normalImagCovector (q i) (z i)) U b
    H Hs ε ℓ t T c M δ x (by linarith) hHs.le hε hε1
    ((profileFrequencyScale_ge_one g φ x).trans hℓ) ht2 hT hc hM.le hδ hδ1 hδκ hMr
    (fun i => (hq i).1) hx hy hcov hφbound
    (fun j => (normalized_real_growth_bounds
      (lt_of_lt_of_le zero_lt_one (profileFrequencyScale_ge_one g φ x)) hℓ hε.le hε1 hHs.le
      (fderiv ℝ φ x) (hslope φ hφ x hx) j).1)
    hcenter hloc (fun i => hend i (2/t) hrad htre hsqrt) ?_ hbudget hb
  intro i hi
  exact hang (q i) (hq i) (z i) x (hz i).1 (hi.trans hinvra)
    ((hz i).2.trans (hsqrt.trans htra)) ℓ hℓ hℓ'
end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.compact_metric_packet_sign_gain_oai := @OAI.YauCounterexamples.compact_metric_packet_sign_gain_oai
