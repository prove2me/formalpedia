-- Prove2me | solution 1 for OAI.YauCounterexamples.physical_finite_superposition_complete_supported
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:23:01.374074+00:00
-- url     : https://prove2.me/submissions/0aef47ac-4ad5-4b8e-994d-d5e8ab2ae613

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_normal_family_canonical_smallBall_uniform
import Theorems.Thm_OAI_YauCounterexamples_uniform_coordinate_packets_with_endpoint_ratios_supported

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ActualHessianForm
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
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma real_phase_linear_general (z : Fin 3 → ℂ) (v : PhaseSpace) :
    (∑ i, (v i : ℂ)*z i).re = inner ℝ v (phaseRealVector z) := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Pi.star_apply, star_trivial, phaseRealVector, mul_comm]

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
lemma contDiff_metricChristoffel (g : SmoothMetric E E) : ContDiff ℝ ∞ (metricChristoffel g) := by
  have hG := contDiff_selfMetricFlat g
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x hG.contDiffAt
  have hD := hG.fderiv_right (m := ∞) (by simp)
  have hDf : ContDiff ℝ ∞ (fun x => (fderiv ℝ (selfMetricFlat g) x).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.comp hD
  have hK : ContDiff ℝ ∞ (fun x => coordinateKoszul (fderiv ℝ (selfMetricFlat g) x)) :=
    (hD.add hDf |>.sub (contDiff_const.clm_comp hDf)).const_smul (1/2 : ℝ)
  exact (contDiff_const.clm_apply hGi).clm_comp hK

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
local instance normalTriNorm_rfef8de_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
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

local instance frameDualNorm_rfef8de_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.YauCounterexamples.frameDualSpace
local instance frameFormNorm_rfef8de_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance frameFormSpace_rfef8de_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffSmoothFiniteWave
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
open Set
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.normalFamilyVecNorm
attribute [local instance] OAI.YauCounterexamples.normalFamilyVecSpace
attribute [local instance] OAI.YauCounterexamples.normalFamilyBiVecNorm
attribute [local instance] OAI.YauCounterexamples.normalFamilyBiVecSpace
attribute [local instance] OAI.YauCounterexamples.normalFamilyDualNorm
attribute [local instance] OAI.YauCounterexamples.normalFamilyDualSpace
local instance normalFamilyFormNorm_rfef8de_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance normalFamilyFormSpace_rfef8de_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
lemma contDiff_frameChristoffel (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (fun q : E × (E →L[ℝ] E) =>
      (metricChristoffel g q.1).bilinearComp q.2 q.2) := by
  have h1 : ContDiff ℝ ∞ (fun q : E × (E →L[ℝ] E) => (metricChristoffel g q.1).comp q.2) :=
    ((contDiff_metricChristoffel g).comp contDiff_fst).clm_comp contDiff_snd
  have h2 := (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearMap.contDiff.comp h1
  have h3 := h2.clm_comp contDiff_snd
  exact (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearMap.contDiff.comp h3

lemma contDiff_normalJetFamily (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E =>
      normalJetMap q.1.1 q.1.2 ((metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) q.2) := by
  have hC : ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E => (metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) :=
    (contDiff_frameChristoffel g).comp contDiff_fst
  exact (contDiff_fst.fst.add (contDiff_fst.snd.clm_apply contDiff_snd)).sub
    ((hC.clm_apply contDiff_snd |>.clm_apply contDiff_snd).const_smul (1/2 : ℝ))

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
open scoped Topology ContDiff
variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma normal_iteratedFDeriv_comp_clm_at (L : F →L[ℝ] E) {f : E → G} {x : F} (n : ℕ)
    (hf : ContDiffAt ℝ n f (L x)) :
    iteratedFDeriv ℝ n (f ∘ L) x =
      (iteratedFDeriv ℝ n f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨U,hU,hu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨V,hVU,hVo,hx⟩ := mem_nhds_iff.mp hU
  have he := L.iteratedFDerivWithin_comp_right (hu.mono hVU) hVo.uniqueDiffOn
    (hVo.preimage L.continuous).uniqueDiffOn hx (le_refl (n : WithTop ℕ∞))
  rw [iteratedFDerivWithin_of_isOpen n hVo hx,
    iteratedFDerivWithin_of_isOpen n (hVo.preimage L.continuous) hx] at he
  exact he

lemma parameter_iteratedFDeriv (f : P × E → F) (t : P) (x : E) (n : ℕ)
    (hf : ContDiffAt ℝ n f (t,x)) :
    iteratedFDeriv ℝ n (fun y => f (t,y)) x =
      (iteratedFDeriv ℝ n f (t,x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  let L := ContinuousLinearMap.inr ℝ P E
  let q : P × E → F := fun z => f ((t,0)+z)
  have hq : ContDiffAt ℝ n q (L x) := by
    have hg : ContDiffAt ℝ n (fun z : P × E => (t,0)+z) (L x) := by fun_prop
    exact (show ContDiffAt ℝ n f ((t,0)+L x) by simpa [L] using hf).comp (L x) hg
  have hj := normal_iteratedFDeriv_comp_clm_at L n hq
  simpa [q,L,Function.comp_def,iteratedFDeriv_comp_add_left] using hj

lemma continuousAt_parameter_iteratedFDeriv (f : P × E → F) {z : P × E} (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f z) :
    ContinuousAt (fun w : P × E => iteratedFDeriv ℝ n (fun y => f (w.1,y)) w.2) z := by
  have hc := (ContinuousMultilinearMap.continuous_precomp
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ P E)).continuousAt.comp
      (hf.continuousAt_iteratedFDeriv (k := n) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))
  apply hc.congr_of_eventuallyEq
  filter_upwards [(hf.of_le (show (n : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).eventually (by simp)] with w hw
  exact parameter_iteratedFDeriv f w.1 w.2 n hw


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
open scoped Topology ContDiff
section ParameterDerivative
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma continuous_parameter_iteratedFDeriv (f : P × E → F) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    Continuous (fun q : P × E => iteratedFDeriv ℝ k (fun x => f (q.1,x)) q.2) :=
  continuous_iff_continuousAt.mpr (fun _ => continuousAt_parameter_iteratedFDeriv f k hf.contDiffAt)
end ParameterDerivative

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
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ComplexRealResponse
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
open Set MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal Topology Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma measurable_complexRealResponse {ι : Type*} (J : Fin 3 → ι → ℂ) :
    Measurable (complexRealResponse J) := by
  unfold complexRealResponse
  fun_prop

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_FiniteGaussianSuperpositionSmallBall
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
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
universe uFinWaves
namespace YauCounterexamples

lemma finite_gaussian_superposition_smallBall {I : Type uFinWaves} [Fintype I]
    (J : I → Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ) (b : (Fin 1 ⊕ Fin 3) → ℝ)
    (i₀ : I) (r : ℝ) (q : ℝ≥0∞)
    (hsmall : ∀ (Ω : Type uFinWaves) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (J i₀) v.2+noise v.1 ∈ Metric.closedBall 0 r} ≤ q) :
    (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
      {γ | (∑ i, complexRealResponse (J i) (γ i))+b ∈ Metric.closedBall 0 r} ≤ q := by
  classical
  let O := {i : I // i ≠ i₀}
  let S := {i : I // ¬i ≠ i₀}
  let ν := Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)
  let μ := Measure.pi (fun _ : O => ν)
  let f := fun γ : I → Fin 3 → ℂ => ((fun i : O => γ i), γ i₀)
  have hf : MeasurePreserving f (Measure.pi (fun _ : I => ν)) (μ.prod ν) := by
    have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : I => ν) (fun i => i ≠ i₀)
    have he := measurePreserving_eval (fun _ : S => ν) (⟨i₀,by simp⟩ : S)
    exact ((MeasurePreserving.id μ).prod he).comp hp
  let noise : (O → Fin 3 → ℂ) → ((Fin 1 ⊕ Fin 3) → ℝ) :=
    fun γ => (∑ i : O, complexRealResponse (J i) (γ i))+b
  have hn : Measurable noise := by
    dsimp only [noise]
    exact (Finset.measurable_sum _ (fun i _ =>
      (measurable_complexRealResponse _).comp (measurable_pi_apply i))).add measurable_const
  have hm : MeasurableSet {v : (O → Fin 3 → ℂ) × (Fin 3 → ℂ) |
      complexRealResponse (J i₀) v.2+noise v.1 ∈ Metric.closedBall 0 r} :=
    ((measurable_complexRealResponse _).comp measurable_snd |>.add
      (hn.comp measurable_fst)) Metric.isClosed_closedBall.measurableSet
  have hsum (γ : I → Fin 3 → ℂ) :
      (∑ i : O, complexRealResponse (J i) (γ i))+complexRealResponse (J i₀) (γ i₀) =
      ∑ i, complexRealResponse (J i) (γ i) := by
    have hs : (∑ i : S, complexRealResponse (J i) (γ i)) =
        complexRealResponse (J i₀) (γ i₀) := by
      apply (Fintype.sum_eq_single (⟨i₀,by simp⟩ : S) ?_).trans rfl
      intro i hi
      exact (hi (Subtype.ext (Classical.not_not.mp i.2))).elim
    simpa only [←hs] using Fintype.sum_subtype_add_sum_subtype (fun i => i ≠ i₀)
      (fun i => complexRealResponse (J i) (γ i))
  have heq : f ⁻¹' {v | complexRealResponse (J i₀) v.2+noise v.1 ∈ Metric.closedBall 0 r} =
      {γ | (∑ i, complexRealResponse (J i) (γ i))+b ∈ Metric.closedBall 0 r} := by
    ext γ
    change complexRealResponse (J i₀) (γ i₀)+
      ((∑ i : O, complexRealResponse (J i) (γ i))+b) ∈ Metric.closedBall 0 r ↔ _
    rw [←add_assoc,add_comm (complexRealResponse (J i₀) (γ i₀)),hsum]
    rfl
  rw [←heq,hf.measure_preimage hm.nullMeasurableSet]
  exact hsmall _ μ noise hn

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_UniformJetBoundsFiberComp
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
open Set Filter
open scoped Topology ContDiff
variable {P E F V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma compact_fiber_jet_bound (ψ : P × E → F) (hψ : ContDiff ℝ (∞ : WithTop ℕ∞) ψ)
    {L : Set (P × E)} (hL : IsCompact L) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ w ∈ L, ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i (fun y => ψ (w.1,y)) w.2‖ ≤ D := by
  let B := fun w : P × E => ∑ i ∈ Finset.range (m+1),
    ‖iteratedFDeriv ℝ i (fun y => ψ (w.1,y)) w.2‖
  have hB : Continuous B := continuous_finsetSum _
    (fun i _ => (continuous_parameter_iteratedFDeriv ψ hψ i).norm)
  obtain ⟨C,hC⟩ := hL.exists_bound_of_continuousOn hB.continuousOn
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro w hw i hi
  calc
    _ ≤ B w := Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
    _ ≤ ‖B w‖ := le_abs_self _
    _ ≤ C := hC w hw
    _ ≤ max 1 C := le_max_right _ _

end

open Set Filter
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormIteratedFDerivCompLinear
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
open Set Filter
open scoped ContDiff Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

lemma realWaveJet_add (n W : ℝ) {u v : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    realWaveJet n W (fun y => u y+v y) x = realWaveJet n W u x+realWaveJet n W v x := by
  ext i
  rcases i with i|i <;> simp [realWaveJet,fderiv_fun_add hu hv,mul_add]

lemma realWaveJet_sum {I : Type*} [Fintype I] (n W : ℝ)
    {u : I → (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) :
    realWaveJet n W (fun y => ∑ i, u i y) x = ∑ i, realWaveJet n W (u i) x := by
  ext j
  rcases j with j|j <;>
    simp [realWaveJet,fderiv_fun_sum (fun i _ => hu i),Finset.mul_sum]

lemma fderiv_re_const_mul {u : (Fin 3 → ℝ) → ℂ} {x : Fin 3 → ℝ}
    (hu : DifferentiableAt ℝ u x) (γ : ℂ) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => (γ*u y).re) x v = (γ*fderiv ℝ u x v).re := by
  have h := (Complex.reCLM.hasFDerivAt.comp x (hu.hasFDerivAt.const_mul γ)).fderiv
  exact congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L v) h

lemma realWaveJet_re_const_mul (n W : ℝ) {u : (Fin 3 → ℝ) → ℂ} {x : Fin 3 → ℝ}
    (hu : DifferentiableAt ℝ u x) (γ : ℂ) :
    realWaveJet n W (fun y => (γ*u y).re) x =
      fun i => (γ*complexWaveJet n (W : ℂ) u x i).re := by
  ext i
  rcases i with i|i
  · simp only [realWaveJet,complexWaveJet,Sum.elim_inl,←Complex.ofReal_inv]
    simp [Complex.mul_re,Complex.mul_im]
    ring
  · simp only [realWaveJet,complexWaveJet,Sum.elim_inr,←Complex.ofReal_inv,
      fderiv_re_const_mul hu γ,waveDeriv]
    simp [Complex.mul_re,Complex.mul_im]
    ring

lemma realWaveJet_three (n W : ℝ) (U : Fin 3 → (Fin 3 → ℝ) → ℂ)
    {x : Fin 3 → ℝ} (hU : ∀ ℓ, DifferentiableAt ℝ (U ℓ) x) (γ : Fin 3 → ℂ) :
    realWaveJet n W (fun y => ∑ ℓ, (γ ℓ*U ℓ y).re) x =
      complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) γ := by
  have hd (ℓ : Fin 3) : DifferentiableAt ℝ (fun y => (γ ℓ*U ℓ y).re) x :=
    Complex.reCLM.differentiableAt.comp x ((hU ℓ).const_mul (γ ℓ))
  rw [realWaveJet_sum n W hd]
  ext i
  simp only [Finset.sum_apply,realWaveJet_re_const_mul n W (hU _) _,complexRealResponse]

lemma realWaveJet_comp_bound (n W : ℝ) {u : (Fin 3 → ℝ) → ℝ}
    {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {x : Fin 3 → ℝ}
    (hu : DifferentiableAt ℝ u (F x)) (hF : DifferentiableAt ℝ F x) :
    ‖realWaveJet n W (u ∘ F) x‖ ≤
      max 1 (3*‖fderiv ℝ F x‖)*‖realWaveJet n W u (F x)‖ := by
  let J := realWaveJet n W u (F x)
  have hJ0 : 0 ≤ ‖J‖ := norm_nonneg _
  have hconst : 1 ≤ max 1 (3*‖fderiv ℝ F x‖) := le_max_left _ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) hJ0)).mpr
  intro i
  rcases i with i|i
  · change ‖W⁻¹*u (F x)‖ ≤ _
    exact (norm_le_pi_norm J (Sum.inl i)).trans (le_mul_of_one_le_left hJ0 hconst)
  · rw [realWaveJet,Sum.elim_inr,fderiv_comp x hu hF,ContinuousLinearMap.comp_apply]
    have hv : fderiv ℝ F x (Pi.single i 1) =
        ∑ j : Fin 3, (fderiv ℝ F x (Pi.single i 1) j) • Pi.single j 1 := by
      ext j
      simp [Pi.single_apply]
    rw [hv,map_sum,Finset.mul_sum]
    have hsum : ‖∑ j : Fin 3, n⁻¹*W⁻¹*fderiv ℝ u (F x)
        (fderiv ℝ F x (Pi.single i 1) j • Pi.single j 1)‖ ≤
        ∑ _j : Fin 3, ‖fderiv ℝ F x‖*‖J‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul,smul_eq_mul]
      have heq : n⁻¹*W⁻¹*(fderiv ℝ F x (Pi.single i 1) j*
          fderiv ℝ u (F x) (Pi.single j 1)) =
          fderiv ℝ F x (Pi.single i 1) j * J (Sum.inr j) := by dsimp [J,realWaveJet]; ring
      rw [heq,norm_mul]
      apply mul_le_mul (le_trans (norm_le_pi_norm _ j) ?_) (norm_le_pi_norm J (.inr j))
        (norm_nonneg _) (norm_nonneg _)
      simpa only [Pi.norm_single,norm_one,mul_one] using (fderiv ℝ F x).le_opNorm (Pi.single i 1)
    calc
      _ ≤ ∑ _j : Fin 3, ‖fderiv ℝ F x‖*‖J‖ := hsum
      _ = (3*‖fderiv ℝ F x‖)*‖J‖ := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hJ0

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
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

lemma contDiff_finiteWaveSuperposition {E I : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : E → ℝ} {U : I → Fin 3 → E → ℂ}
    (hw : ContDiff ℝ ∞ w) (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) : ContDiff ℝ ∞ (finiteWaveSuperposition w U γ) :=
  hw.add (ContDiff.sum (fun i _ => ContDiff.sum (fun ℓ _ =>
    Complex.reCLM.contDiff.comp (contDiff_const.mul (hU i ℓ)))))

lemma realWaveJet_finiteWaveSuperposition {I : Type*} [Fintype I]
    (n W : ℝ) (w : (Fin 3 → ℝ) → ℝ) (U : I → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hw : ContDiff ℝ ∞ w) (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) (x : Fin 3 → ℝ) :
    realWaveJet n W (finiteWaveSuperposition w U γ) x =
      (∑ i, complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U i ℓ) x) (γ i))+
        realWaveJet n W w x := by
  have hd (i) : DifferentiableAt ℝ (fun y => ∑ ℓ, (γ i ℓ*U i ℓ y).re) x :=
    DifferentiableAt.fun_sum (fun ℓ _ => Complex.reCLM.differentiableAt.comp x
      (((hU i ℓ).differentiable (by simp) x).const_mul (γ i ℓ)))
  unfold finiteWaveSuperposition
  rw [realWaveJet_add n W (hw.differentiable (by simp) x)
    (DifferentiableAt.fun_sum (fun i _ => hd i)),realWaveJet_sum n W hd]
  simp only [realWaveJet_three n W _ (fun ℓ => (hU _ ℓ).differentiable (by simp) x) _]
  exact add_comm _ _

theorem finite_superposition_pullback_smallBall {I : Type} [Fintype I]
    (n W : ℝ) (w : (Fin 3 → ℝ) → ℝ) (U : I → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hw : ContDiff ℝ ∞ w) (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (hF : ContDiff ℝ ∞ F) (x : Fin 3 → ℝ)
    (M : ℝ) (hM : max 1 (3*‖fderiv ℝ F x‖) ≤ M)
    (i₀ : I) (r : ℝ) (q : ℝ≥0∞)
    (hsmall : ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U i₀ ℓ ∘ F) x) v.2+
          noise v.1 ∈ Metric.closedBall 0 (M*r)} ≤ q) :
    (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
      {γ | ‖realWaveJet n W (finiteWaveSuperposition w U γ) (F x)‖ ≤ r} ≤ q := by
  let J : I → Fin 3 → ((Fin 1 ⊕ Fin 3) → ℂ) :=
    fun i ℓ => complexWaveJet n (W : ℂ) (U i ℓ ∘ F) x
  have h := finite_gaussian_superposition_smallBall J (realWaveJet n W (w ∘ F) x)
    i₀ (M*r) q hsmall
  apply le_trans (measure_mono ?_) h
  intro γ hγ
  change (∑ i, complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U i ℓ ∘ F) x) (γ i))+
    realWaveJet n W (w ∘ F) x ∈ Metric.closedBall 0 (M*r)
  rw [←realWaveJet_finiteWaveSuperposition n W (w ∘ F) (fun i ℓ => U i ℓ ∘ F)
    (hw.comp hF) (fun i ℓ => (hU i ℓ).comp hF)]
  rw [Metric.mem_closedBall,dist_zero_right]
  change ‖realWaveJet n W ((finiteWaveSuperposition w U γ) ∘ F) x‖ ≤ M*r
  have hb := realWaveJet_comp_bound n W
    ((contDiff_finiteWaveSuperposition hw hU γ).differentiable (by simp) (F x))
    (hF.differentiable (by simp) x)
  exact hb.trans ((mul_le_mul_of_nonneg_right hM (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hγ (le_trans (by norm_num) ((le_max_left _ _).trans hM))))

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
open Set
open Set
open scoped ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ComplexWaveJetGerm
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
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma complexWaveJet_germ {u v : (Fin 3 → ℝ) → ℂ} {x : Fin 3 → ℝ}
    (h : u =ᶠ[𝓝 x] v) (n : ℝ) (W : ℂ) :
    complexWaveJet n W u x = complexWaveJet n W v x := by
  ext i
  rcases i with i|i
  · simp only [complexWaveJet,Sum.elim_inl,h.eq_of_nhds]
  · simp only [complexWaveJet,Sum.elim_inr,waveDeriv,h.fderiv_eq]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalCoordinateMap
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

lemma contDiff_normalCoordinateMap (g : SmoothMetric NormalWaveSpace NormalWaveSpace) :
    ContDiff ℝ ∞ (fun w : NormalWaveParameter × (Fin 3 → ℝ) => normalCoordinateMap g w.1 w.2) :=
  normalWaveEquiv.symm.contDiff.comp ((contDiff_normalJetFamily g).comp
    (contDiff_fst.prodMk (normalWaveEquiv.contDiff.comp contDiff_snd)))

lemma normalCoordinateMap_derivative_bound
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ M ≥ 1, ∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ ≤ 1 →
      max 1 (3*‖fderiv ℝ (normalCoordinateMap g q) x‖) ≤ M := by
  let F := fun w : NormalWaveParameter × (Fin 3 → ℝ) => normalCoordinateMap g w.1 w.2
  have hF : ContDiff ℝ ∞ F := contDiff_normalCoordinateMap g
  obtain ⟨C,hC⟩ := ((metricFrameSet_isCompact g hK).prod
    (isCompact_closedBall (0 : Fin 3 → ℝ) 1)).exists_bound_of_continuousOn
      ((continuous_parameter_iteratedFDeriv F hF 1).continuousOn)
  refine ⟨max 1 (3*C),le_max_left _ _,?_⟩
  intro q hq x hx
  have hb := hC (q,x) ⟨hq,by simpa [Metric.mem_closedBall,dist_zero_right] using hx⟩
  rw [norm_iteratedFDeriv_one] at hb
  exact max_le_max le_rfl (mul_le_mul_of_nonneg_left hb (by norm_num))

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

lemma normalWaveProfile_gradient_pairing
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (q : NormalWaveParameter)
    (v : NormalWaveSpace) :
    inner ℝ (gradient (normalWaveProfile g φ q) 0) v = fderiv ℝ φ q.1 (q.2 v) := by
  rw [inner_gradient_left]
  exact normalJetMap_first_phase_jet q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)
    (fun v w => metricChristoffel_symm g q.1 (q.2 v) (q.2 w)) hφ v

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
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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

lemma frame_inverse_apply (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K)
    (v : NormalWaveSpace) : q.2 (q.2.inverse v) = v := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  rw [←hA,ContinuousLinearMap.inverse_equiv]
  exact A.apply_symm_apply v

lemma normalPhaseCovector_re (q : NormalWaveParameter) (z : Fin 3 → ℂ)
    (v : NormalWaveSpace) :
    (normalPhaseCovector q z v).re = inner ℝ (q.2.inverse v) (phaseRealVector z) := by
  rw [normalPhaseCovector_apply]
  exact real_phase_linear_general z (q.2.inverse v)

lemma normalPhaseCovector_real_error (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K)
    (z : Fin 3 → ℂ) :
    ‖Complex.reCLM.comp (normalPhaseCovector q z)-fderiv ℝ φ q.1‖ ≤
      ‖q.2.inverse‖*‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  have hv : fderiv ℝ φ q.1 v =
      inner ℝ (gradient (normalWaveProfile g φ q) 0) (q.2.inverse v) := by
    rw [normalWaveProfile_gradient_pairing g hφ,frame_inverse_apply g hq]
  change |(normalPhaseCovector q z v).re-fderiv ℝ φ q.1 v| ≤ _
  rw [normalPhaseCovector_re,hv,real_inner_comm (q.2.inverse v) (gradient (normalWaveProfile g φ q) 0),←inner_sub_right]
  calc
    _ ≤ ‖q.2.inverse v‖*‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖q.2.inverse‖*‖v‖)*‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ :=
      mul_le_mul_of_nonneg_right (q.2.inverse.le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

lemma compact_fderiv_displacement_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q ∈ K, ∀ x : E, ‖x-q‖ ≤ 1 →
      ‖fderiv ℝ f x-fderiv ℝ f q‖ ≤ C*‖x-q‖ := by
  let H := fun w : E × E => fderiv ℝ f (w.1+w.2)
  have hH : ContDiff ℝ ∞ H := (hf.fderiv_right (m := ∞) (by simp)).comp
    (contDiff_fst.add contDiff_snd)
  obtain ⟨C,hC,hb⟩ := compact_fiber_jet_bound H hH (hK.prod (isCompact_closedBall 0 1)) 1
  refine ⟨C,hC,?_⟩
  intro q hq x hx
  have hd (v) (hv : v ∈ Metric.closedBall (0 : E) 1) :
      ‖fderiv ℝ (fun t => H (q,t)) v‖ ≤ C := by
    rw [←norm_iteratedFDeriv_one]
    exact hb (q,v) ⟨hq,hv⟩ 1 le_rfl
  have hu : ContDiff ℝ ∞ (fun t => H (q,t)) := hH.comp (contDiff_const.prodMk contDiff_id)
  have hh := (convex_closedBall (0 : E) 1).norm_image_sub_le_of_norm_fderiv_le
    (fun v _ => hu.differentiable (by simp) v) hd (Metric.mem_closedBall_self zero_le_one)
    (show x-q ∈ Metric.closedBall (0 : E) 1 by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)
  simpa only [H,add_zero,add_sub_cancel,sub_zero] using hh

theorem compact_normal_real_slope_error (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ C > 0, ∀ q ∈ metricFrameSet g K, ∀ z : Fin 3 → ℂ,
      ∀ x : NormalWaveSpace, ‖x-q.1‖ ≤ 1 →
      ‖Complex.reCLM.comp (normalPhaseCovector q z)-fderiv ℝ φ x‖ ≤
        C*(‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖+‖x-q.1‖) := by
  obtain ⟨R,hR,hb⟩ := metricFrameSet_inverse_bound g hK
  obtain ⟨D,hD,hd⟩ := compact_fderiv_displacement_bound φ hφ hK
  refine ⟨R+D,by linarith,?_⟩
  intro q hq z x hx
  have h1 := (normalPhaseCovector_real_error g hφ hq z).trans
    (mul_le_mul_of_nonneg_right (hb q hq) (norm_nonneg _))
  have h2 := hd q.1 hq.1 x hx
  rw [norm_sub_rev] at h2
  have htriangle : ‖Complex.reCLM.comp (normalPhaseCovector q z)-fderiv ℝ φ x‖ ≤
      ‖Complex.reCLM.comp (normalPhaseCovector q z)-fderiv ℝ φ q.1‖ +
      ‖fderiv ℝ φ q.1-fderiv ℝ φ x‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le
      (Complex.reCLM.comp (normalPhaseCovector q z)-fderiv ℝ φ q.1)
      (fderiv ℝ φ q.1-fderiv ℝ φ x)
  have h := htriangle.trans (add_le_add h1 h2)
  refine h.trans ?_
  nlinarith [norm_nonneg (phaseRealVector z-gradient (normalWaveProfile g φ q) 0),
    norm_nonneg (x-q.1)]

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RealImagCovector
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples



open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

lemma covector_real_replacement_error (L : NormalWaveSpace →L[ℝ] ℂ)
    (a : NormalWaveSpace →L[ℝ] ℝ) :
    ‖L-realImagCovector a (Complex.imCLM.comp L)‖ ≤ ‖Complex.reCLM.comp L-a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  have heq : (L-realImagCovector a (Complex.imCLM.comp L)) v =
      ((Complex.reCLM.comp L-a) v : ℂ) := by
    apply Complex.ext <;>
      simp [realImagCovector,Complex.mul_re,Complex.mul_im]
  rw [heq,Complex.norm_real]
  exact (Complex.reCLM.comp L-a).le_opNorm v

lemma exp_realImagCovector (a b : NormalWaveSpace →L[ℝ] ℝ) (n : ℝ) (v : NormalWaveSpace) :
    Complex.exp ((n : ℂ)*realImagCovector a b v) =
      (Real.exp (n*a v) : ℂ)*Complex.exp (((n*b v : ℝ) : ℂ)*Complex.I) := by
  have heq : (n : ℂ)*realImagCovector a b v =
      ((n*a v : ℝ) : ℂ)+((n*b v : ℝ) : ℂ)*Complex.I := by
    simp only [realImagCovector,add_apply,ContinuousLinearMap.comp_apply,
      smul_apply,Complex.ofRealCLM_apply,smul_eq_mul,Complex.ofReal_mul]
    ring
  rw [heq,Complex.exp_add,←Complex.ofReal_exp]

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_UniformCoordinatePacketsCommonSlope2
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Matrix MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
theorem uniform_coordinate_packets_common_slope_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {V : Set NormalWaveSpace} (hV : IsOpen V) (hKV : K ⊆ V)
    :
    ∃ (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
      (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
      (e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace),
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ b ∧
      (∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0) ∧
      (∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0) ∧
      (∀ q, (e q : NormalWaveSpace → NormalWaveSpace) =
        normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
    ∀ (B C : ℝ) {κ : ℝ}, 0 < κ → ∀ m D : ℕ,
    ∃ ρ > 0,
      (∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ < ρ → normalWaveEquiv x ∈ (e q).source) ∧
      ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ U : NormalWaveParameter → (Fin 3 → ℂ) → ComplexPhaseMatrix → ℝ → NormalWaveSpace → ℂ,
      ∃ T > 0, ∃ c > 0, ∃ r₀ > 0, ∃ M > 0,
        (∀ q ∈ metricFrameSet g K, ∀ z Q n, tsupport (U q z Q n) ⊆ V) ∧
        (∀ q z Q n x, normalWaveEquiv x ∈ (e q).source →
          U q z Q n (e q (normalWaveEquiv x)) = normalFamilyWave g φ A b q z Q ζ m D n x) ∧
      ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix),
        ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
        (∀ n : ℝ, 1 ≤ n →
          ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
          ContDiff ℝ ∞ (U q z Q n) ∧ HasCompactSupport (U q z Q n) ∧
          U q z Q n q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U q z Q n) y‖ ≤
              T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q z Q n) w +
              (n : ℂ)*((n : ℂ)+2)*U q z Q n w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        (∀ (n r : ℝ), 1 ≤ n → 0 ≤ r → r < r₀ → (Real.sqrt n)⁻¹ ≤ r →
          ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
          ∀ x y : NormalWaveSpace, ‖x-q.1‖ ≤ r → ‖y-q.1‖ ≤ r → n*‖y-x‖ ≤ 1 →
          ‖U q z Q n y-
              (Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
                Complex.exp (((n*normalImagCovector q z (y-x) : ℝ) : ℂ)*Complex.I)*U q z Q n x‖ ≤
            (M*r)*‖(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
                Complex.exp (((n*normalImagCovector q z (y-x) : ℝ) : ℂ)*Complex.I)*U q z Q n x‖) := by
  obtain ⟨Cs,hCs,hslope⟩ := compact_normal_real_slope_error g hφ hK
  obtain ⟨A,b,e,hA,hb,hA0,hAd,he,hfact⟩ := uniform_coordinate_packets_with_endpoint_ratios_supported g φ hφ hK hV hKV
  refine ⟨A,b,e,hA,hb,hA0,hAd,he,?_⟩
  intro B C κ hκ m D
  obtain ⟨ρ,hρ,hsource,hfactory⟩ := hfact B C hκ m D
  refine ⟨ρ,hρ,hsource,?_⟩
  intro ζ hζ hcζ hsζ hζ0
  obtain ⟨U,T,hT,c,hc,re,hre,Ce,hCe,hSupport,hformula,hU⟩ := hfactory ζ hζ hcζ hsζ hζ0
  let M := Ce+2*Cs
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨U,T,hT,c,hc,min re (min 1 (1/(2*M))),
    lt_min hre (lt_min zero_lt_one (by positivity)),10*M,by positivity,hSupport,hformula,?_⟩
  intro q hq z Q hz hnQ hQ
  refine ⟨(hU q hq z Q hz hnQ hQ).1,?_⟩
  intro n r hn hr hrr hnr hlin x y hx hy hsep
  have hrre : r < re := hrr.trans_le (min_le_left _ _)
  have hr1 : r ≤ 1 := (hrr.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hrM : M*r ≤ 1/2 := by
    have hh : r < 1/(2*M) := hrr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (lt_div_iff₀ (show 0 < 2*M by positivity)).mp hh
    nlinarith
  let L := realImagCovector (fderiv ℝ φ x) (normalImagCovector q z)
  have hL : ‖normalPhaseCovector q z-L‖ ≤ 2*Cs*r := by
    have hh := (covector_real_replacement_error (normalPhaseCovector q z) (fderiv ℝ φ x)).trans
      (hslope q hq z x (hx.trans hr1))
    exact hh.trans (by nlinarith [hlin.trans hnr])
  have heps : Ce*r+2*Cs*r ≤ 1/2 := by dsimp [M] at hrM; nlinarith
  have hh := (hU q hq z Q hz hnQ hQ).2 n r (2*Cs*r) hn hr hrre
    (by positivity) x y hx hy hsep L hL heps
  rw [show L = realImagCovector (fderiv ℝ φ x) (normalImagCovector q z) from rfl,
    exp_realImagCovector] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PhysicalFiniteSuperpositionCompleteSupported
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Matrix MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
theorem physical_triple_packets_complete_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {V : Set NormalWaveSpace} (hV : IsOpen V) (hKV : K ⊆ V)
    (hnc : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 ≠ 0 → ∃ v,
      inner ℝ (gradient (normalWaveProfile g φ q) 0) v = 0 ∧
      ‖v‖^2 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 ∧
      0 < actualHessianForm (normalWaveProfile g φ q) (gradient (normalWaveProfile g φ q) 0)
        (gradient (normalWaveProfile g φ q) 0)+actualHessianForm (normalWaveProfile g φ q) v v)
    (hcrit : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 = 0 →
      ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (normalWaveProfile g φ q) v v)
    (m D : ℕ) :
    ∃ (e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace),
      (∀ q, (e q : NormalWaveSpace → NormalWaveSpace) =
        normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
    ∃ ρ > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
    ∃ T > 0, ∃ c > 0, ∃ M > 0, ∃ C₀ > 0, ∃ r₀ > 0, ∃ rₑ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ q ∈ metricFrameSet g K, ∀ n : ℝ, N ≤ n →
      ∃ (z : Fin 3 → Fin 3 → ℂ) (U : Fin 3 → NormalWaveSpace → ℂ),
        (∀ ℓ, tsupport (U ℓ) ⊆ V) ∧
        (∀ ℓ, (∑ i, z ℓ i*z ℓ i = -1) ∧
          ‖phaseRealVector (z ℓ)-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
        (∀ ℓ, ContDiff ℝ ∞ (U ℓ) ∧ HasCompactSupport (U ℓ) ∧
          U ℓ q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U ℓ) w +
              (n : ℂ)*((n : ℂ)+2)*U ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        (∀ ℓ (r : ℝ), 0 ≤ r → r < rₑ → (Real.sqrt n)⁻¹ ≤ r →
          ∀ x y : NormalWaveSpace, ‖x-q.1‖ ≤ r → ‖y-q.1‖ ≤ r → n*‖y-x‖ ≤ 1 →
          ‖U ℓ y-(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector q (z ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U ℓ x‖ ≤
          (M*r)*‖(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector q (z ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U ℓ x‖) ∧
        ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
        ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*φ (e q (normalWaveEquiv x))) →
        let W := Real.exp (n*φ (e q (normalWaveEquiv x)))+R
        ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
        (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ)
            (fun t => U ℓ (e q (normalWaveEquiv t))) x) v.2+noise v.1 ∈
            Metric.closedBall 0 r} ≤ ENNReal.ofReal (C₀*n^28*r^4) := by
  obtain ⟨A,b,e,hA,hb,hA0,hAd,he,hfactory⟩ := uniform_coordinate_packets_common_slope_supported g φ hφ hK hV hKV
  obtain ⟨κ,hκ,C,hC,B,hB,hsmall⟩ := normal_family_canonical_smallBall_uniform g φ hφ hK
    A b hA hb hA0 hAd hnc hcrit
  obtain ⟨ρ,hρ,hsrc,hwaves⟩ := hfactory B C hκ m D
  refine ⟨e,he,ρ,hρ,?_⟩
  intro ζ hζ hcζ hsζ hζ0
  obtain ⟨U,T,hT,c,hc,re,hre,M,hM,hSupport,hformula,hest⟩ := hwaves ζ hζ hcζ hsζ hζ0
  obtain ⟨r₁,hr₁,C₀,hC₀,N,hN,hs⟩ := hsmall ζ hζ0 m D
  refine ⟨T,hT,c,hc,M,hM,C₀,hC₀,min r₁ ρ,lt_min hr₁ hρ,re,hre,N,hN,?_⟩
  intro q hq n hn
  obtain ⟨z,Q,hz,hnull,hQ,hdev,hlaw⟩ := hs q hq n hn
  let Z : Fin 3 → NormalWaveSpace → ℂ := fun ℓ => U q (z ℓ) (Q ℓ) n
  refine ⟨z,Z,(fun ℓ => hSupport q hq (z ℓ) (Q ℓ) n),(fun ℓ => ⟨hnull ℓ,hdev ℓ⟩),
    (fun ℓ => (hest q hq (z ℓ) (Q ℓ) (hz ℓ) (hnull ℓ) (hQ ℓ)).1
      n (hN.trans hn) (hdev ℓ)),?_,?_⟩
  · intro ℓ r hr hrr hnr x y hx hy hsep
    exact (hest q hq (z ℓ) (Q ℓ) (hz ℓ) (hnull ℓ) (hQ ℓ)).2 n r
      (hN.trans hn) hr hrr hnr (hdev ℓ) x y hx hy hsep
  intro x hx hxn R hR0 hR
  dsimp only
  intro Ω _ μ _ noise hnoise r hr
  have hxsrc : normalWaveEquiv x ∈ (e q).source := hsrc q hq x (hx.trans_le (min_le_right _ _))
  have hjet (ℓ : Fin 3) (W : ℂ) :
      complexWaveJet n W (fun t => Z ℓ (e q (normalWaveEquiv t))) x =
        complexWaveJet n W (normalFamilyWave g φ A b q (z ℓ) (Q ℓ) ζ m D n) x := by
    apply complexWaveJet_germ
    filter_upwards [( (e q).open_source.preimage normalWaveEquiv.continuous).mem_nhds hxsrc] with t ht
    exact hformula q (z ℓ) (Q ℓ) n t ht
  simp_rw [hjet]
  have hR' : R ≤ n^6*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x)) := by
    simpa only [he,normalWaveProfile] using hR
  simpa only [he,normalWaveProfile] using
    hlaw x (hx.trans_le (min_le_left _ _)) hxn R hR0 hR' Ω μ noise hnoise r hr

end


open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
theorem physical_finite_superposition_complete_supported_oai
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O)
    (hnc : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 ≠ 0 → ∃ v,
      inner ℝ (gradient (normalWaveProfile g φ q) 0) v = 0 ∧
      ‖v‖^2 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 ∧
      0 < actualHessianForm (normalWaveProfile g φ q) (gradient (normalWaveProfile g φ q) 0)
        (gradient (normalWaveProfile g φ q) 0)+actualHessianForm (normalWaveProfile g φ q) v v)
    (hcrit : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 = 0 →
      ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (normalWaveProfile g φ q) v v)
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
  classical
  obtain ⟨e,he,ρ,hρ,hfam⟩ := physical_triple_packets_complete_supported g φ hφ hK hO hKO hnc hcrit m D
  obtain ⟨M,hM,hMb⟩ := normalCoordinateMap_derivative_bound g hK
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  refine ⟨ρ,hρ,?_⟩
  intro ζ hζ hcζ hsζ hζ0
  obtain ⟨T,hT,c,hc,M₀,hM₀,C₀,hC₀,r₀,hr₀,rₑ,hrₑ,N,hN,hdata⟩ := hfam ζ hζ hcζ hsζ hζ0
  refine ⟨T,hT,c,hc,M₀,hM₀,C₀*M^4,mul_pos hC₀ (pow_pos hM0 _),r₀,hr₀,rₑ,hrₑ,N,hN,?_⟩
  intro n hn
  choose z U hSupport hz hU hend hlaw using (fun q : metricFrameSet g K => hdata q q.property n hn)
  refine ⟨z,U,hSupport,hz,hU,hend,?_⟩
  intro I _ p w hw i₀ x hxr hxn
  dsimp only
  intro R hR0 hR r hr
  let F := normalCoordinateMap g (p i₀)
  have hF : ContDiff ℝ ∞ F := (contDiff_normalCoordinateMap g).comp
    (contDiff_const.prodMk contDiff_id)
  have hx1 : ‖x‖ ≤ 1 := hxn.trans (by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) (hN.trans hn))
  have hfe (t : Fin 3 → ℝ) : normalWaveEquiv (F t) = e (p i₀) (normalWaveEquiv t) := by
    simp only [F,normalCoordinateMap,ContinuousLinearEquiv.apply_symm_apply,he]
  let W := Real.exp (n*φ (normalWaveEquiv (F x)))+R
  have hR' : R ≤ n^6*Real.exp (n*φ (e (p i₀) (normalWaveEquiv x))) := by
    simpa only [←hfe] using hR
  have hsmall := hlaw (p i₀) x hxr hxn R hR0 hR'
  have h := finite_superposition_pullback_smallBall n W (w ∘ normalWaveEquiv)
    (fun i ℓ => U (p i) ℓ ∘ normalWaveEquiv) (hw.comp normalWaveEquiv.contDiff)
    (fun i ℓ => (hU (p i) ℓ).1.comp normalWaveEquiv.contDiff) F hF x M
    (hMb (p i₀) (p i₀).property x hx1) i₀ r
    (ENNReal.ofReal (C₀*n^28*(M*r)^4)) ?_
  · convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  · intro Ω _ μ _ noise hnoise
    have hs := hsmall Ω μ noise hnoise (M*r) (mul_nonneg hM0.le hr)
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Function.comp_def,hfe,W]


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.physical_finite_superposition_complete_supported_oai := @OAI.YauCounterexamples.physical_finite_superposition_complete_supported_oai
