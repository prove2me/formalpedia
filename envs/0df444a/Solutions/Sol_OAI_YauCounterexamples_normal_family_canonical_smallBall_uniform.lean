-- Prove2me | solution 1 for OAI.YauCounterexamples.normal_family_canonical_smallBall_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:21:05.082664+00:00
-- url     : https://prove2.me/submissions/abc7fb39-0654-4dd6-b296-ea839b7b68cb

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_canonical_phase_triple_smallBall
import Theorems.Thm_OAI_YauCounterexamples_compact_profile_three_phase_data

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
section SecondJetBridge
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hessianFromJet_iterated (f : E → F) (x : E) :
    hessianFromJet (iteratedFDeriv ℝ 2 f x) = fderiv ℝ (fderiv ℝ f) x := by
  ext v w
  change (iteratedFDeriv ℝ 2 f x) (Fin.cons v (fun _ => w)) = _
  simpa using iteratedFDeriv_two_apply (𝕜 := ℝ) f x (Fin.cons v (fun _ => w))

lemma continuous_hessian_of_iterated {X : Type*} [TopologicalSpace X]
    (f : X → E → F)
    (hf : Continuous (fun q : X × E => iteratedFDeriv ℝ 2 (f q.1) q.2)) :
    Continuous (fun q : X × E => fderiv ℝ (fderiv ℝ (f q.1)) q.2) := by
  simpa only [Function.comp_def, hessianFromJet_iterated] using hessianFromJet.continuous.comp hf

end SecondJetBridge



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PhaseFormMatrix
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

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
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
open Matrix Set Filter
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma complexPhaseVector_square (a b : EuclideanSpace ℝ ι)
    (hab : inner ℝ a b = 0) (hs : inner ℝ b b = 1 + inner ℝ a a) :
    complexPhaseVector a b ⬝ᵥ complexPhaseVector a b = -1 := by
  have ha : (∑ i, a i * a i) = inner ℝ a a := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial]
  have hb : (∑ i, b i * b i) = inner ℝ b b := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial]
  have hab' : (∑ i, a i * b i) = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using hab
  apply Complex.ext
  · simp only [dotProduct, complexPhaseVector, Complex.re_sum, Complex.mul_re,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, add_zero, zero_add,
      sub_zero, Complex.mul_im, Complex.neg_re, Complex.one_re,
      Finset.sum_sub_distrib, ha, hb]
    linarith
  · simp only [dotProduct, complexPhaseVector, Complex.im_sum, Complex.mul_re,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, add_zero, zero_add,
      sub_zero, Complex.mul_im, Complex.neg_im, Complex.one_im,
      Finset.sum_add_distrib, mul_comm, hab']
    norm_num




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RealPhaseLinear
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
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise

lemma shifted_phase_square {a ν b : PhaseSpace} (hνb : inner ℝ ν b = 0)
    (ha : a = ‖a‖ • ν) (hb : ‖b‖^2 = 1 + ‖a‖^2) (δ : ℝ) :
    complexPhaseVector (a + δ • ν) (shiftedPhaseImag a ν b δ) ⬝ᵥ
      complexPhaseVector (a + δ • ν) (shiftedPhaseImag a ν b δ) = -1 := by
  apply complexPhaseVector_square
  · simp only [shiftedPhaseImag, inner_smul_right, inner_add_left,
      inner_smul_left, conj_trivial, hνb, mul_zero, add_zero]
    rw [ha, inner_smul_left, conj_trivial, hνb, mul_zero, mul_zero]
  · simp only [real_inner_self_eq_norm_sq, shiftedPhaseImag, norm_smul,
      Real.norm_eq_abs, sq_abs, mul_pow, div_pow, hb]
    rw [Real.sq_sqrt (show 0 ≤ 1 + ‖a + δ • ν‖^2 by positivity),
      Real.sq_sqrt (show 0 ≤ 1 + ‖a‖^2 by positivity)]
    have hn : (1 : ℝ) + ‖a‖^2 ≠ 0 := by positivity
    field_simp


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
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise



end YauCounterexamples
end

end OAI
end

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

lemma continuous_actualHessianForm {X : Type*} [TopologicalSpace X]
    (φ : X → PhaseSpace → ℝ)
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2)) :
    Continuous (fun p => phaseFormMatrix (actualHessianForm (φ p))) := by
  have hH := (continuous_hessian_of_iterated φ hφ2).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : X => (0 : PhaseSpace))))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (hH.clm_apply continuous_const).clm_apply continuous_const

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

local instance frameDualNorm_r85d128_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.YauCounterexamples.frameDualSpace
local instance frameFormNorm_r85d128_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance frameFormSpace_r85d128_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
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

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffSmoothFiniteWave
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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
local instance normalFamilyFormNorm_r85d128_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance normalFamilyFormSpace_r85d128_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
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
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma normal_profile_family_smooth (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun q : NormalWaveParameter × NormalWaveSpace =>
      φ (normalJetMap q.1.1 q.1.2 ((metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) q.2)) :=
  hφ.comp (contDiff_normalJetFamily g)


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PhaseDensityInvBound
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
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YauCounterexamples

lemma phase_density_inv_bound (η c n δ : ℝ) (hη : 0 < η) (hc : 0 < c)
    (hn : 1 ≤ n) (hδ : 0 < δ) (hδsq : δ^2 = 1/n) :
    (Real.sqrt η/2*δ*(c/2*(n^6)⁻¹)^4)⁻¹ ≤
      (Real.sqrt η/2*(c/2)^4)⁻¹*n^28 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have heq : δ^2*n = 1 := (eq_div_iff hn0.ne').mp hδsq
  have hδ1 : δ ≤ 1 := by
    have hh : δ^2 ≤ 1 := by rw [hδsq]; exact (div_le_one hn0).mpr hn
    nlinarith
  have hinv : δ⁻¹ ≤ n := by
    rw [← one_div]
    apply (div_le_iff₀ hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδ1 (mul_nonneg hn0.le hδ.le)]
  have hid : (Real.sqrt η/2*δ*(c/2*(n^6)⁻¹)^4)⁻¹ =
      (Real.sqrt η/2*(c/2)^4)⁻¹*δ⁻¹*n^24 := by
    field_simp
  rw [hid]
  calc
    _ ≤ (Real.sqrt η/2*(c/2)^4)⁻¹*n*n^24 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv (by positivity)) (by positivity)
    _ = (Real.sqrt η/2*(c/2)^4)⁻¹*n^25 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn (by omega)) (by positivity)

lemma phase_density_power_bound (η c n δ r : ℝ) (hη : 0 < η) (hc : 0 < c)
    (hn : 1 ≤ n) (hδ : 0 < δ) (hδsq : δ^2 = 1/n) (hr : 0 ≤ r) :
    ENNReal.ofReal (Real.sqrt η/2*δ*(c/2*(n^6)⁻¹)^4)⁻¹*(ENNReal.ofReal (2*r))^4 ≤
      ENNReal.ofReal (16*(Real.sqrt η/2*(c/2)^4)⁻¹*n^28*r^4) := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*r),← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((Real.sqrt η/2*(c/2)^4)⁻¹*n^28)*(2*r)^4 :=
      mul_le_mul_of_nonneg_right (phase_density_inv_bound η c n δ hη hc hn hδ hδsq) (by positivity)
    _ = _ := by ring

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsAlignedUnit
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
open Set Filter Matrix
open scoped Topology Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma exists_aligned_unit (a : PhaseSpace) : ∃ ν : PhaseSpace, ‖ν‖ = 1 ∧ a = ‖a‖ • ν := by
  by_cases ha : a = 0
  · refine ⟨EuclideanSpace.single 0 1,by simp,?_⟩
    simp [ha]
  · refine ⟨‖a‖⁻¹ • a,?_,?_⟩
    · rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]
    · rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha),one_smul]

lemma complexPhaseVector_norm_bound (a b : PhaseSpace) :
    ‖complexPhaseVector a b‖ ≤ ‖a‖+‖b‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    _ ≤ ‖(a i : ℂ)‖+‖Complex.I*(b i : ℂ)‖ := norm_add_le _ _
    _ = ‖a i‖+‖b i‖ := by simp
    _ ≤ _ := add_le_add (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _)

lemma three_phase_real_deviation (a ν b c d : PhaseSpace) (δ : ℝ)
    (hν : ‖ν‖ = 1) (hδ : 0 ≤ δ) :
    ∀ ℓ : Fin 3, ‖phaseRealVector
      (![complexPhaseVector a b,complexPhaseVector a c,complexPhaseVector (a+δ • ν) d] ℓ)-a‖ ≤ δ := by
  intro ℓ
  fin_cases ℓ <;> simp [norm_smul,Real.norm_of_nonneg hδ,hν,hδ]

lemma phase_length_bound (a b : PhaseSpace) (hb : ‖b‖^2 = 1+‖a‖^2) :
    ‖b‖ ≤ ‖a‖+1 := by
  nlinarith [norm_nonneg a,norm_nonneg b]

lemma shiftedPhaseImag_norm_sq (a ν b : PhaseSpace) (δ : ℝ)
    (hb : ‖b‖^2 = 1+‖a‖^2) :
    ‖shiftedPhaseImag a ν b δ‖^2 = 1+‖a+δ • ν‖^2 := by
  simp only [shiftedPhaseImag,norm_smul,Real.norm_eq_abs,sq_abs,mul_pow,div_pow,hb]
  rw [Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
  have hn : (1 : ℝ)+‖a‖^2 ≠ 0 := by positivity
  field_simp

theorem ThreePhaseData.bounded_spec {H : RealForm PhaseSpace} {a ν : PhaseSpace}
    {δ κ η C A : ℝ} (h : ThreePhaseData H a ν δ κ η C)
    (hν : ‖ν‖ = 1) (halign : a = ‖a‖ • ν) (hA : 0 ≤ A) (ha : ‖a‖ ≤ A)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∃ b c : PhaseSpace, inner ℝ ν b = 0 ∧ inner ℝ ν c = 0 ∧
      ‖b‖^2 = 1+‖a‖^2 ∧ ‖c‖^2 = 1+‖a‖^2 ∧
      ‖b‖ ≤ A+1 ∧ ‖c‖ ≤ A+1 ∧ η ≤ transverseAngleSq b c ∧
      let z := ![complexPhaseVector a b,complexPhaseVector a c,
        complexPhaseVector (a+δ • ν) (shiftedPhaseImag a ν b δ)]
      ∃ Q : Fin 3 → ComplexPhaseMatrix, (∀ ℓ, ‖z ℓ‖ ≤ 2*A+3) ∧
        (∀ ℓ, ∑ i, z ℓ i*z ℓ i = -1) ∧
        (∀ ℓ, PhaseMatrixValid H (z ℓ) κ C (Q ℓ)) := by
  obtain ⟨b,c,hb,hc,hbn,hcn,hang,⟨Q₀,hQ₀⟩,⟨Q₁,hQ₁⟩,⟨Q₂,hQ₂⟩⟩ := h
  have hbA : ‖b‖ ≤ A+1 := by
    apply (sq_le_sq₀ (norm_nonneg b) (add_nonneg hA zero_le_one)).mp
    rw [hbn]
    nlinarith [(sq_le_sq₀ (norm_nonneg a) hA).mpr ha]
  have hcA : ‖c‖ ≤ A+1 := (phase_length_bound a c hcn).trans (by linarith)
  have had : ‖a+δ • ν‖ ≤ A+1 := by
    calc
      _ ≤ ‖a‖+‖δ • ν‖ := norm_add_le _ _
      _ = ‖a‖+δ := by rw [norm_smul,Real.norm_of_nonneg hδ,hν,mul_one]
      _ ≤ _ := by linarith
  have hd : ‖shiftedPhaseImag a ν b δ‖ ≤ A+2 :=
    (phase_length_bound _ _ (shiftedPhaseImag_norm_sq a ν b δ hbn)).trans (by linarith)
  refine ⟨b,c,hb,hc,hbn,hcn,hbA,hcA,hang,![Q₀,Q₁,Q₂],?_,?_,?_⟩
  · intro ℓ
    fin_cases ℓ
    · simpa using
        (complexPhaseVector_norm_bound a b).trans (by linarith : ‖a‖+‖b‖ ≤ 2*A+3)
    · simpa using
        (complexPhaseVector_norm_bound a c).trans (by linarith : ‖a‖+‖c‖ ≤ 2*A+3)
    · simpa using
        (complexPhaseVector_norm_bound (a+δ • ν) (shiftedPhaseImag a ν b δ)).trans
          (by linarith : ‖a+δ • ν‖+‖shiftedPhaseImag a ν b δ‖ ≤ 2*A+3)
  · have hab : inner ℝ a b = 0 := by rw [halign,inner_smul_left]; simp [hb]
    have hac : inner ℝ a c = 0 := by rw [halign,inner_smul_left]; simp [hc]
    intro ℓ
    fin_cases ℓ
    · exact complexPhaseVector_square a b hab (by simpa only [real_inner_self_eq_norm_sq] using hbn)
    · exact complexPhaseVector_square a c hac (by simpa only [real_inner_self_eq_norm_sq] using hcn)
    · exact shifted_phase_square hb halign hbn δ
  · intro ℓ
    fin_cases ℓ
    · exact hQ₀
    · exact hQ₁
    · exact hQ₂

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactProfileCanonicalSmallBall
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
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise

lemma actualHessianForm_symm (φ : PhaseSpace → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    (actualHessianForm φ).IsSymm := by
  constructor
  intro v w
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))).eq v w

lemma inverse_sqrt_eventually_small {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
      1 ≤ n ∧ 0 < (Real.sqrt n)⁻¹ ∧ (Real.sqrt n)⁻¹ < ε ∧
        ((Real.sqrt n)⁻¹)^2 = 1/n := by
  have ht : Tendsto (fun n : ℝ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨max 1 N,le_max_left _ _,?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn1
  refine ⟨hn1,inv_pos.mpr (Real.sqrt_pos.mpr hn0),hN n ((le_max_right _ _).trans hn),?_⟩
  rw [inv_pow,Real.sq_sqrt hn0.le,one_div]


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
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
theorem compact_profile_canonical_smallBall_uniform_orders {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b₀ : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb₀ : ∀ p i, ContDiff ℝ ∞ (b₀ p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b₀ q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (ha : Continuous (fun p => gradient (φ p) 0))
    (hnc : ∀ p, gradient (φ p) 0 ≠ 0 → ∃ b,
      inner ℝ (gradient (φ p) 0) b = 0 ∧ ‖b‖^2 = 1+‖gradient (φ p) 0‖^2 ∧
      0 < actualHessianForm (φ p) (gradient (φ p) 0) (gradient (φ p) 0)+actualHessianForm (φ p) b b)
    (hcrit : ∀ p, gradient (φ p) 0 = 0 → ∃ P : Submodule ℝ PhaseSpace,
      Module.finrank ℝ P = 2 ∧ ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (φ p) v v)
    :
    ∃ κ > 0, ∃ C > 0, ∃ B > 0,
    ∀ (F : X → (Fin 3 → ℝ) → ℂ) (_hF : ∀ p, ContDiff ℝ ∞ (F p))
    (_hF0 : ∀ p, F p 0 = (φ p 0 : ℂ))
    (_hFc : ∀ k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (F q.1) q.2))
    (ζ : (Fin 3 → ℝ) → ℂ) (_hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ),
    ∃ r₀ > 0, ∃ K > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ p (n : ℝ), N ≤ n → ∃ (z : Fin 3 → Fin 3 → ℂ) (Q : Fin 3 → ComplexPhaseMatrix),
        (∀ ℓ, ‖z ℓ‖ ≤ B) ∧ (∀ ℓ, ∑ i, z ℓ i*z ℓ i = -1) ∧
        (∀ ℓ, PhaseMatrixValid (actualHessianForm (φ p)) (z ℓ) κ C (Q ℓ)) ∧
        (∀ ℓ, ‖phaseRealVector (z ℓ)-gradient (φ p) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
      let U := fun ℓ => canonicalCutoffWave (g p) (b₀ p) (φ p 0 : ℂ) (z ℓ) (Q ℓ) ζ m D n
      ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
      ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*(F p x).re) →
      let W := Real.exp (n*(F p x).re)+R
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) v.2+noise v.1 ∈
          Metric.closedBall 0 r} ≤ ENNReal.ofReal (K*n^28*r^4) := by
  let a := fun p => gradient (φ p) 0
  obtain ⟨δ₀,hδ₀,κ,hκ,η,hη,C,hC,hdata⟩ := compact_profile_three_phase_data
    (fun p => actualHessianForm (φ p)) a (continuous_actualHessianForm φ hφ2) ha
    (fun p => actualHessianForm_symm (φ p) (hφ p)) hnc hcrit
  obtain ⟨A₀,hA₀⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuousOn
  let A := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hAa (p) : ‖a p‖ ≤ A := (hA₀ p (mem_univ p)).trans (le_max_left _ _)
  refine ⟨κ,hκ,C,hC,2*A+3,by positivity,?_⟩
  intro F hF hF0 hFc ζ hζ m D
  obtain ⟨r₀,hr₀,c₀,hc₀,ε,hε,hsmall⟩ := canonical_phase_triple_smallBall g b₀ hg hb₀ hg0 hdg0 hgc hbc
    φ hφ0 hφ2 F hF hF0 hFc (2*A+3) C κ (A+1) η (by linarith) hη ζ hζ m D
  obtain ⟨N,hN,hthreshold⟩ := inverse_sqrt_eventually_small (lt_min hδ₀ (lt_min hε zero_lt_one))
  refine ⟨r₀,hr₀,
    16*(Real.sqrt η/2*(c₀/2)^4)⁻¹,by positivity,N,hN,?_⟩
  intro p n hn
  obtain ⟨hn1,hδ,hδsmall,hδsq⟩ := hthreshold n hn
  let δ := (Real.sqrt n)⁻¹
  have hδ₀le : δ ≤ δ₀ := (hδsmall.trans_le (min_le_left _ _)).le
  have hδε : δ < ε := hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := (hδsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  obtain ⟨ν,hν,halign⟩ := exists_aligned_unit (a p)
  obtain ⟨b,c,hb,hc,hbn,hcn,hbA,hcA,hang,Q,hz,hnull,hQ⟩ :=
    (hdata p ν hν halign δ ⟨hδ.le,hδ₀le⟩).bounded_spec hν halign hA (hAa p) hδ.le hδ1
  let z := ![complexPhaseVector (a p) b,complexPhaseVector (a p) c,
    complexPhaseVector (a p+δ • ν) (shiftedPhaseImag (a p) ν b δ)]
  refine ⟨z,Q,hz,hnull,hQ,three_phase_real_deviation (a p) ν b c
    (shiftedPhaseImag (a p) ν b δ) δ hν hδ.le,?_⟩
  dsimp only
  intro x hxr hx R hR0 hR Ω _ μ _ noise hnoise r hr
  exact (hsmall p n δ hn1 hδ hδε hδsq (a p) ν b c (shiftedPhaseImag (a p) ν b δ)
    ((hAa p).trans (by linarith)) hν hb hc hbn hcn hbA hcA hang Q hz hnull hQ
    x hxr hx R hR0 hR Ω μ noise hnoise r hr).trans
      (phase_density_power_bound η c₀ n δ r hη hc₀ hn1 hδ hδsq hr)



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ContinuousGradientIterated
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
namespace YauCounterexamples
lemma continuous_gradient_of_iterated {X : Type*} [TopologicalSpace X]
    (φ : X → PhaseSpace → ℝ)
    (hφ1 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 1 (φ q.1) q.2)) :
    Continuous (fun p => gradient (φ p) 0) := by
  have he (p : X) : (continuousMultilinearCurryFin1 ℝ PhaseSpace ℝ)
      (iteratedFDeriv ℝ 1 (φ p) 0) = fderiv ℝ (φ p) 0 := by
    ext v
    exact iteratedFDeriv_one_apply (fun _ => v)
  unfold gradient
  exact (InnerProductSpace.toDual ℝ PhaseSpace).symm.continuous.comp (by
    simpa only [Function.comp_def,id_eq,he] using
      (continuousMultilinearCurryFin1 ℝ PhaseSpace ℝ).continuous.comp
        (hφ1.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : X => (0 : PhaseSpace))))))
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_AdmissibleCutoffWaveLocalizedDerivatives
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma contDiff_normalWaveProfile (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun w : NormalWaveParameter × PhaseSpace => normalWaveProfile g φ w.1 w.2) :=
  normal_profile_family_smooth g φ hφ

lemma continuous_normalWaveProfile_iteratedFDeriv
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Set NormalWaveSpace) (k : ℕ) :
    Continuous (fun w : (metricFrameSet g K) × PhaseSpace =>
      iteratedFDeriv ℝ k (normalWaveProfile g φ w.1.val) w.2) := by
  have h : Continuous (fun w : NormalWaveParameter × PhaseSpace =>
      iteratedFDeriv ℝ k (normalWaveProfile g φ w.1) w.2) :=
    continuous_parameter_iteratedFDeriv
      (fun w : NormalWaveParameter × PhaseSpace => normalWaveProfile g φ w.1 w.2)
      (contDiff_normalWaveProfile g hφ) k
  exact h.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

end

open Set Filter Matrix
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_NormalFamilyCanonicalSmallBall
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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

theorem normal_family_canonical_smallBall_uniform_oai
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
    (hA0 : ∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0)
    (hAd : ∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0)
    (hnc : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 ≠ 0 → ∃ v,
      inner ℝ (gradient (normalWaveProfile g φ q) 0) v = 0 ∧
      ‖v‖^2 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 ∧
      0 < actualHessianForm (normalWaveProfile g φ q) (gradient (normalWaveProfile g φ q) 0)
        (gradient (normalWaveProfile g φ q) 0)+actualHessianForm (normalWaveProfile g φ q) v v)
    (hcrit : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 = 0 →
      ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (normalWaveProfile g φ q) v v) :
    ∃ κ > 0, ∃ C > 0, ∃ B > 0,
    ∀ (ζ : (Fin 3 → ℝ) → ℂ) (_hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ),
    ∃ r₀ > 0, ∃ C₀ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ q ∈ metricFrameSet g K, ∀ (n : ℝ), N ≤ n → ∃ (z : Fin 3 → Fin 3 → ℂ) (Q : Fin 3 → ComplexPhaseMatrix),
        (∀ ℓ, ‖z ℓ‖ ≤ B) ∧ (∀ ℓ, ∑ i, z ℓ i*z ℓ i = -1) ∧
        (∀ ℓ, PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) (z ℓ) κ C (Q ℓ)) ∧
        (∀ ℓ, ‖phaseRealVector (z ℓ)-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
      let U := fun ℓ => normalFamilyWave g φ A b q (z ℓ) (Q ℓ) ζ m D n
      ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
      ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x)) →
      let W := Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x))+R
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) v.2+noise v.1 ∈
          Metric.closedBall 0 r} ≤ ENNReal.ofReal (C₀*n^28*r^4) := by
  let X := metricFrameSet g K
  let : CompactSpace X := isCompact_iff_compactSpace.mp (metricFrameSet_isCompact g hK)
  let G : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ := fun q i j x => A (q.val,x) i j
  let β : X → Fin 3 → (Fin 3 → ℝ) → ℂ := fun q j x => b (q.val,x) j
  let Φ : X → PhaseSpace → ℝ := fun q => normalWaveProfile g φ q.val
  have hG (q : X) (i j : Fin 3) : ContDiff ℝ ∞ (G q i j) :=
    (contDiff_pi.mp (contDiff_pi.mp hA i) j).comp (contDiff_const.prodMk contDiff_id)
  have hβ (q : X) (j : Fin 3) : ContDiff ℝ ∞ (β q j) :=
    (contDiff_pi.mp hb j).comp (contDiff_const.prodMk contDiff_id)
  have hG0 (q : X) (i j : Fin 3) : G q i j 0 = if i = j then 1 else 0 := hA0 q.val q.property i j
  have hGd (q : X) (i j : Fin 3) : fderiv ℝ (G q i j) 0 = 0 := hAd q.val q.property i j
  have hGc (i j : Fin 3) (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (G w.1 i j) w.2) := by
    exact (continuous_parameter_iteratedFDeriv (fun w => A w i j)
      (contDiff_pi.mp (contDiff_pi.mp hA i) j) k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hβc (j : Fin 3) (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (β w.1 j) w.2) := by
    exact (continuous_parameter_iteratedFDeriv (fun w => b w j)
      (contDiff_pi.mp hb j) k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hΦ (q : X) : ContDiff ℝ ∞ (Φ q) :=
    (contDiff_normalWaveProfile g hφ).comp (contDiff_const.prodMk contDiff_id)
  have hΦ0 : Continuous (fun q : X => Φ q 0) :=
    (contDiff_normalWaveProfile g hφ).continuous.comp
      (continuous_subtype_val.prodMk continuous_const)
  have hΦ2 : Continuous (fun w : X × PhaseSpace => iteratedFDeriv ℝ 2 (Φ w.1) w.2) :=
    continuous_normalWaveProfile_iteratedFDeriv g hφ K 2
  have ha : Continuous (fun q : X => gradient (Φ q) 0) :=
    continuous_gradient_of_iterated Φ (continuous_normalWaveProfile_iteratedFDeriv g hφ K 1)
  obtain ⟨κ,hκ,C,hC,B,hB,hsmall⟩ := compact_profile_canonical_smallBall_uniform_orders
    G β hG hβ hG0 hGd hGc hβc Φ hΦ hΦ0 hΦ2 ha
    (fun q => hnc q.val q.property) (fun q => hcrit q.val q.property)
  refine ⟨κ,hκ,C,hC,B,hB,?_⟩
  intro ζ hζ m D
  let F : X → (Fin 3 → ℝ) → ℂ := fun q x => (Φ q (normalWaveEquiv x) : ℂ)
  have hF (q : X) : ContDiff ℝ ∞ (F q) :=
    Complex.ofRealCLM.contDiff.comp ((hΦ q).comp normalWaveEquiv.contDiff)
  have hF0 (q : X) : F q 0 = (Φ q 0 : ℂ) := by simp [F]
  have hFc (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (F w.1) w.2) := by
    have hf : ContDiff ℝ ∞ (fun w : NormalWaveParameter × (Fin 3 → ℝ) =>
        (normalWaveProfile g φ w.1 (normalWaveEquiv w.2) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((contDiff_normalWaveProfile g hφ).comp
        (contDiff_fst.prodMk (normalWaveEquiv.contDiff.comp contDiff_snd)))
    exact (continuous_parameter_iteratedFDeriv _ hf k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨r₀,hr₀,C₀,hC₀,N,hN,hs⟩ := hsmall F hF hF0 hFc ζ hζ m D
  refine ⟨r₀,hr₀,C₀,hC₀,N,hN,?_⟩
  intro q hq n hn
  simpa only [normalFamilyWave,F,G,β,Φ,Complex.ofReal_re] using hs ⟨q,hq⟩ n hn

end YauCounterexamples

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.YauCounterexamples.normal_family_canonical_smallBall_uniform_oai.{u_1} := @OAI.YauCounterexamples.normal_family_canonical_smallBall_uniform_oai.{u_1}
