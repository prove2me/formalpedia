-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_normal_wave_chart_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:28:22.902934+00:00
-- url     : https://prove2.me/submissions/03d27c72-5710-4569-a89f-21324e44c741

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

omit [FiniteDimensional ℝ E] in
lemma normalJetMap_remainder (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (x y : E) :
    normalJetMap p A C x - normalJetMap p A C y - A (x-y) =
      -(1/2 : ℝ) • (C x (x-y) + C (x-y) y) := by
  simp only [normalJetMap, map_sub, _root_.sub_apply, smul_add, smul_sub]
  module

lemma normalJetMap_derivative_invertible (A : E ≃L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) {x : E}
    (hx : ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖x‖ < 1) :
    (A.toContinuousLinearMap - C x).IsInvertible := by
  have hi : Function.Injective (A.toContinuousLinearMap - C x) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    change A v - C x v = 0 at hv
    have he : A v = C x v := sub_eq_zero.mp hv
    have hh : ‖v‖ ≤ (‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖x‖) * ‖v‖ := by
      calc
        ‖v‖ = ‖A.symm (A v)‖ := by rw [A.symm_apply_apply]
        _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ‖A v‖ := (A.symm : E →L[ℝ] E).le_opNorm _
        _ = ‖(A.symm : E →L[ℝ] E)‖ * ‖C x v‖ := by rw [he]
        _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * (‖C x‖ * ‖v‖) := by gcongr; exact (C x).le_opNorm _
        _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ((‖C‖ * ‖x‖) * ‖v‖) := by gcongr; exact C.le_opNorm _
        _ = _ := by ring
    have hn : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp hn
  let e := LinearEquiv.ofBijective (A.toContinuousLinearMap - C x).toLinearMap
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

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

local instance frameDualNorm_r323dd0_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.YauCounterexamples.frameDualSpace
local instance frameFormNorm_r323dd0_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance frameFormSpace_r323dd0_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
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
local instance normalFamilyFormNorm_r323dd0_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance normalFamilyFormSpace_r323dd0_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalInverseVecNorm
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
open scoped Topology ContDiff
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_open_inverse {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ (∞ : WithTop ℕ∞) f s) (hinj : InjOn f s)
    (hd : ∀ x ∈ s, (fderiv ℝ f x).IsInvertible) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ e.source = s ∧
      ContDiffOn ℝ (∞ : WithTop ℕ∞) e.symm e.target := by
  have hop : ∀ t : Set E, IsOpen t → t ⊆ s → IsOpen (f '' t) := by
    intro t ht hts
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨D,hD⟩ := hd x (hts hx)
    have hfc : ContDiffAt ℝ (∞ : WithTop ℕ∞) f x := (hf x (hts hx)).contDiffAt (hs.mem_nhds (hts hx))
    have hfd : HasFDerivAt f (D : E →L[ℝ] F) x := by
      rw [hD]
      exact (hfc.differentiableAt (by simp)).hasFDerivAt
    let e := hfc.toOpenPartialHomeomorph f hfd (by simp)
    have hxe : x ∈ e.source := hfc.mem_toOpenPartialHomeomorph_source hfd (by simp)
    have hmem : f x ∈ e '' (e.source ∩ t) := ⟨x,⟨hxe,hx⟩,rfl⟩
    apply Filter.mem_of_superset ((e.isOpen_image_source_inter ht).mem_nhds hmem)
    rintro _ ⟨y,hy,rfl⟩
    exact ⟨y,hy.2,rfl⟩
  let p := hinj.toPartialEquiv f s
  have ho : IsOpenMap (s.domRestrict f) := by
    intro t ht
    have hv : IsOpen (Subtype.val '' t : Set E) := hs.isOpenMap_subtype_val t ht
    have hz := hop (Subtype.val '' t) hv (by rintro _ ⟨a,ha,rfl⟩; exact a.property)
    change IsOpen ((fun x : s => f x) '' t)
    simpa only [Set.image_image] using hz
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict p hf.continuousOn ho hs
  refine ⟨e,rfl,rfl,?_⟩
  intro y hy
  obtain ⟨D,hD⟩ := hd (e.symm y) (e.map_target hy)
  have hfc : ContDiffAt ℝ (∞ : WithTop ℕ∞) f (e.symm y) :=
    (hf _ (e.map_target hy)).contDiffAt (hs.mem_nhds (e.map_target hy))
  have hfd : HasFDerivAt f (D : E →L[ℝ] F) (e.symm y) := by
    rw [hD]
    exact (hfc.differentiableAt (by simp)).hasFDerivAt
  exact (e.contDiffAt_symm hy hfd hfc).contDiffWithinAt
end

section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma familyTotal_derivative_invertible {f : P × E → E} {q : P} {x : E}
    (hf : DifferentiableAt ℝ f (q,x))
    (hd : (fderiv ℝ (fun y => f (q,y)) x).IsInvertible) :
    (fderiv ℝ (fun a : P × E => (a.1,f a)) (q,x)).IsInvertible := by
  let L := fderiv ℝ f (q,x)
  obtain ⟨D,hD⟩ := hd
  let A : P →L[ℝ] E := L.comp (ContinuousLinearMap.inl ℝ P E)
  let T := (ContinuousLinearEquiv.refl ℝ P).skewProd D A
  have hR : L.comp (ContinuousLinearMap.inr ℝ P E) = D := by
    have h := hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_right q x)
    exact h.fderiv.symm.trans hD.symm
  have hL : (ContinuousLinearMap.fst ℝ P E).prod L = T.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro a
    apply Prod.ext
    · rfl
    · change L a = D a.2 + L (a.1,0)
      have ha : a = (0,a.2) + (a.1,0) := by ext <;> simp
      calc
        L a = L (0,a.2) + L (a.1,0) := by conv_lhs => rw [ha]; rw [L.map_add]
        _ = D a.2 + L (a.1,0) := congrArg (fun v => v + L (a.1,0))
          (congrArg (fun M : E →L[ℝ] E => M a.2) hR)
  refine ⟨T,?_⟩
  exact ((hasFDerivAt_fst.prodMk hf.hasFDerivAt).fderiv.trans hL).symm
end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma isOpen_continuousLinearMap_isInvertible :
    IsOpen {A : E →L[ℝ] E | A.IsInvertible} := by
  have he : {A : E →L[ℝ] E | A.IsInvertible} = {A : E →L[ℝ] E | IsUnit A} := by
    ext A
    constructor
    · rintro ⟨e,rfl⟩
      exact e.toUnit.isUnit
    · rintro ⟨u,rfl⟩
      exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ E u,rfl⟩
  rw [he]
  exact Units.isOpen

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.normalInverseVecNorm
attribute [local instance] OAI.YauCounterexamples.normalInverseVecSpace
local instance normalInverseBiVecNorm_r323dd0_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance normalInverseBiVecSpace_r323dd0_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma normalJetMap_injOn_small (p : E) (A : E ≃L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) :
    InjOn (normalJetMap p A C)
      {x | ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖x‖ < 1/2} := by
  intro x hx y hy he
  change ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖x‖ < 1/2 at hx
  change ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖y‖ < 1/2 at hy
  have hr := normalJetMap_remainder p A C x y
  rw [he,sub_self,zero_sub] at hr
  have hAv : A (x-y) = (1/2 : ℝ) • (C x (x-y) + C (x-y) y) := by
    calc
      _ = -(-(A (x-y))) := (neg_neg _).symm
      _ = _ := by
        change -(-((A : E →L[ℝ] E) (x-y))) = _
        rw [hr]; module
  have hB : ‖x-y‖ ≤
      ((‖(A.symm : E →L[ℝ] E)‖*‖C‖*‖x‖ +
        ‖(A.symm : E →L[ℝ] E)‖*‖C‖*‖y‖)/2) * ‖x-y‖ := by
    calc
      ‖x-y‖ = ‖A.symm (A (x-y))‖ := by rw [A.symm_apply_apply]
      _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ‖A (x-y)‖ := (A.symm : E →L[ℝ] E).le_opNorm _
      _ = ‖(A.symm : E →L[ℝ] E)‖ * ((1/2 : ℝ)*‖C x (x-y)+C (x-y) y‖) := by
        rw [hAv,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ((1/2 : ℝ)*
          ((‖C‖*‖x‖)*‖x-y‖ + (‖C‖*‖x-y‖)*‖y‖)) := by
        gcongr
        calc
          _ ≤ ‖C x (x-y)‖ + ‖C (x-y) y‖ := norm_add_le _ _
          _ ≤ _ := add_le_add ((C x).le_opNorm _ |>.trans
            (mul_le_mul_of_nonneg_right (C.le_opNorm _) (norm_nonneg _)))
            ((C (x-y)).le_opNorm _ |>.trans
            (mul_le_mul_of_nonneg_right (C.le_opNorm _) (norm_nonneg _)))
      _ = _ := by ring
  have hn : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

lemma isOpen_normalFamilySource (g : SmoothMetric E E) : IsOpen (normalFamilySource g) := by
  apply isOpen_iff_mem_nhds.mpr
  intro w hw
  have hI := (isOpen_continuousLinearMap_isInvertible.preimage
    (continuous_snd.comp continuous_fst)).mem_nhds hw.1
  have hi : ContinuousAt (fun w : (E × (E →L[ℝ] E)) × E => w.1.2.inverse) w :=
    (hw.1.contDiffAt_map_inverse (n := (∞ : WithTop ℕ∞))).continuousAt.comp
      (f := fun w : (E × (E →L[ℝ] E)) × E => w.1.2)
      (continuous_snd.comp continuous_fst).continuousAt
  have hC : ContinuousAt (fun w : (E × (E →L[ℝ] E)) × E =>
      (metricChristoffel g w.1.1).bilinearComp w.1.2 w.1.2) w :=
    ((contDiff_frameChristoffel g).comp contDiff_fst).continuous.continuousAt
  have hcn : ContinuousAt (fun z : (E × (E →L[ℝ] E)) × E =>
      ‖(metricChristoffel g z.1.1).bilinearComp z.1.2 z.1.2‖) w := by
    exact hC.norm
  have hm : ContinuousAt (fun z : (E × (E →L[ℝ] E)) × E => ‖z.1.2.inverse‖ *
      ‖(metricChristoffel g z.1.1).bilinearComp z.1.2 z.1.2‖) w := by
    exact hi.norm.mul hcn
  have hf : ContinuousAt (fun z : (E × (E →L[ℝ] E)) × E => ‖z.1.2.inverse‖ *
      ‖(metricChristoffel g z.1.1).bilinearComp z.1.2 z.1.2‖ * ‖z.2‖) w := by
    exact hm.mul continuous_snd.continuousAt.norm
  have hh := hf.eventually (gt_mem_nhds hw.2)
  exact inter_mem hI hh

lemma normalFamilyTotal_injOn (g : SmoothMetric E E) :
    InjOn (normalFamilyTotal g) (normalFamilySource g) := by
  rintro ⟨q,x⟩ hx ⟨q',y⟩ hy he
  have hq : q = q' := congrArg Prod.fst he
  subst q'
  refine Prod.ext (by rfl) ?_
  obtain ⟨A,hA⟩ := hx.1
  have hi : (A.symm : E →L[ℝ] E) = q.2.inverse := by
    rw [←hA,ContinuousLinearMap.inverse_equiv]
  have hh := normalJetMap_injOn_small q.1 A
    ((metricChristoffel g q.1).bilinearComp q.2 q.2)
  apply hh
  · simpa only [mem_ofPred_eq,hi] using hx.2
  · simpa only [mem_ofPred_eq,hi] using hy.2
  · simpa only [normalFamilyTotal,hA] using congrArg Prod.snd he

lemma normalFamilyTotal_smooth (g : SmoothMetric E E) : ContDiff ℝ (∞ : WithTop ℕ∞) (normalFamilyTotal g) :=
  contDiff_fst.prodMk (contDiff_normalJetFamily g)

lemma normalFamilyTotal_derivative_invertible (g : SmoothMetric E E)
    {w : (E × (E →L[ℝ] E)) × E} (hw : w ∈ normalFamilySource g) :
    (fderiv ℝ (normalFamilyTotal g) w).IsInvertible := by
  obtain ⟨A,hA⟩ := hw.1
  let C := (metricChristoffel g w.1.1).bilinearComp w.1.2 w.1.2
  have hi : (A.symm : E →L[ℝ] E) = w.1.2.inverse := by
    rw [←hA,ContinuousLinearMap.inverse_equiv]
  have hs : ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖w.2‖ < 1 := by
    rw [hi]
    exact hw.2.trans (by norm_num)
  have hCs : ∀ v z, C v z = C z v := by
    intro v z
    exact metricChristoffel_symm g w.1.1 (w.1.2 v) (w.1.2 z)
  have hd : (fderiv ℝ (normalJetMap w.1.1 w.1.2 C) w.2).IsInvertible := by
    rw [fderiv_normalJetMap w.1.1 w.1.2 C hCs]
    have h := normalJetMap_derivative_invertible A C hs
    simpa only [hA] using h
  exact familyTotal_derivative_invertible (f := fun a : (E × (E →L[ℝ] E)) × E =>
    normalJetMap a.1.1 a.1.2 ((metricChristoffel g a.1.1).bilinearComp a.1.2 a.1.2) a.2)
    ((contDiff_normalJetFamily g).differentiable (by simp) w) hd

theorem exists_normal_family_inverse (g : SmoothMetric E E) :
    ∃ e : OpenPartialHomeomorph ((E × (E →L[ℝ] E)) × E) ((E × (E →L[ℝ] E)) × E),
      (e : ((E × (E →L[ℝ] E)) × E) → ((E × (E →L[ℝ] E)) × E)) = normalFamilyTotal g ∧
      e.source = normalFamilySource g ∧ ContDiffOn ℝ (∞ : WithTop ℕ∞) e.symm e.target :=
  smooth_open_inverse (isOpen_normalFamilySource g) (normalFamilyTotal_smooth g).contDiffOn
    (normalFamilyTotal_injOn g) (fun _ h => normalFamilyTotal_derivative_invertible g h)

lemma compact_normal_family_radius (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ x ∈ Metric.closedBall (0 : E) r,
      (q,x) ∈ normalFamilySource g := by
  have hsub : metricFrameSet g K ×ˢ {(0 : E)} ⊆ normalFamilySource g := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    have hz : x = 0 := hx
    subst x
    exact ⟨metricFrameSet_equiv g hq,by simp⟩
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma (metricFrameSet_isCompact g hK)
    isCompact_singleton (isOpen_normalFamilySource g) hsub
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  refine ⟨r/2,half_pos hr,?_⟩
  intro q hq x hx
  apply hUV ⟨hKU hq,hrV ?_⟩
  exact (Metric.closedBall_subset_ball (half_lt_self hr)) hx


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_NormalFamilyInverseExtension
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
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem normal_family_inverse_extension (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ r > 0, ∃ e : OpenPartialHomeomorph ((E × (E →L[ℝ] E)) × E) ((E × (E →L[ℝ] E)) × E),
      (e : ((E × (E →L[ℝ] E)) × E) → ((E × (E →L[ℝ] E)) × E)) = normalFamilyTotal g ∧
      e.source = normalFamilySource g ∧ ContDiffOn ℝ (∞ : WithTop ℕ∞) e.symm e.target ∧
      (∀ q ∈ metricFrameSet g K, ∀ x ∈ Metric.closedBall (0 : E) r, (q,x) ∈ e.source) ∧
      ∃ ψ : (E × (E →L[ℝ] E)) × E → E, ContDiff ℝ (∞ : WithTop ℕ∞) ψ ∧
        ∀ q ∈ metricFrameSet g K, ∀ x ∈ Metric.closedBall (0 : E) r,
          (fun y => (e.symm (q,y)).2) =ᶠ[𝓝 (normalJetMap q.1 q.2
            ((metricChristoffel g q.1).bilinearComp q.2 q.2) x)] (fun y => ψ (q,y)) := by
  obtain ⟨e,he,hs,hi⟩ := exists_normal_family_inverse g
  obtain ⟨r,hr,hR⟩ := compact_normal_family_radius g hK
  have hsub : metricFrameSet g K ×ˢ Metric.closedBall (0 : E) r ⊆ e.source := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    rw [hs]
    exact hR q hq x hx
  let L := e '' (metricFrameSet g K ×ˢ Metric.closedBall (0 : E) r)
  have hL : IsCompact L := ((metricFrameSet_isCompact g hK).prod
    (isCompact_closedBall 0 r)).image_of_continuousOn (e.continuousOn.mono hsub)
  have hLt : L ⊆ e.target := by
    rintro _ ⟨w,hw,rfl⟩
    exact e.map_source (hsub hw)
  obtain ⟨ψ,hψ,hEq⟩ := smooth_extension_near_compact hL e.open_target hLt hi.snd
  refine ⟨r,hr,e,he,hs,hi,(fun q hq x hx => hsub ⟨hq,hx⟩),ψ,hψ,?_⟩
  intro q hq x hx
  have hm : e (q,x) ∈ L := ⟨(q,x),⟨hq,hx⟩,rfl⟩
  have hEqx := hEq.filter_mono (nhds_le_nhdsSet hm)
  have ht : Tendsto (fun y : E => (q,y))
      (𝓝 (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x))
      (𝓝 (e (q,x))) := by
    rw [he]
    exact (continuous_const.prodMk continuous_id).continuousAt
  exact hEqx.comp_tendsto ht
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FamilyInverseFst
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
open scoped Topology ContDiff
namespace YauCounterexamples

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiffOn_fiberInverse (e : OpenPartialHomeomorph (P × E) (P × E))
    (he : ∀ w, (e w).1 = w.1) (q : P)
    (hi : ContDiffOn ℝ (∞ : WithTop ℕ∞) e.symm e.target) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞) (fiberOpenPartialHomeomorph e he q).symm
      (fiberOpenPartialHomeomorph e he q).target := by
  exact (hi.comp ((contDiff_const.prodMk contDiff_id).contDiffOn)
    (fun _ hx => hx)).snd
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactFiberLocalCompBound
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
open scoped Topology ContDiff
namespace YauCounterexamples

theorem exists_normal_wave_chart_family_oai (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ r > 0, ∃ e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace,
      (∀ q, (e q : NormalWaveSpace → NormalWaveSpace) =
        normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
      (∀ q, ContDiffOn ℝ ∞ (e q).symm (e q).target) ∧
      (∀ q ∈ metricFrameSet g K, Metric.closedBall (0 : NormalWaveSpace) r ⊆ (e q).source) ∧
      ∃ ψ : NormalWaveParameter × NormalWaveSpace → NormalWaveSpace, ContDiff ℝ ∞ ψ ∧
        ∀ q ∈ metricFrameSet g K, ∀ x ∈ Metric.closedBall (0 : NormalWaveSpace) r,
          (e q).symm =ᶠ[𝓝 (e q x)] (fun y => ψ (q,y)) := by
  obtain ⟨r,hr,e,he,hs,hi,hR,ψ,hψ,hg⟩ := normal_family_inverse_extension g hK
  have he1 : ∀ w, (e w).1 = w.1 := by intro w; rw [he]; rfl
  let eq := fiberOpenPartialHomeomorph e he1
  have heq (q : NormalWaveParameter) : (eq q : NormalWaveSpace → NormalWaveSpace) =
      normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) := by
    funext x
    change (e (q,x)).2 = _
    rw [he]
    rfl
  refine ⟨r,hr,eq,heq,(fun q => contDiffOn_fiberInverse e he1 q hi),?_,ψ,hψ,?_⟩
  · intro q hq x hx
    exact hR q hq x hx
  · intro q hq x hx
    change (fun y => (e.symm (q,y)).2) =ᶠ[𝓝 (eq q x)] (fun y => ψ (q,y))
    rw [heq]
    exact hg q hq x hx
end YauCounterexamples

end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_normal_wave_chart_family_oai := @OAI.YauCounterexamples.exists_normal_wave_chart_family_oai
