-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_three_profile_seed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:16:08.420803+00:00
-- url     : https://prove2.me/submissions/55931f8d-fd30-4854-899a-78742474a0c6

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_threeLogEnvelope_trace

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ScalarLogFirst
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma scalarLog_first {q : E → ℝ} {x : E} (hq : DifferentiableAt ℝ q x) (hx : q x ≠ 0) (v : E) :
    fderiv ℝ (fun y => Real.log (q y)) x v = (q x)⁻¹*fderiv ℝ q x v := by
  rw [(hq.hasFDerivAt.log hx).fderiv]
  rfl
lemma directional_clm_comp_general {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : E →L[ℝ] F) {f : F → V}
    (hf : Differentiable ℝ f) (x v : E) :
    fderiv ℝ (f ∘ L) x v = fderiv ℝ f (L x) (L v) := by
  rw [fderiv_comp x (hf _) L.differentiableAt,L.fderiv]
  rfl
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

lemma roundChart_zero (p : E) (L : F →ₗᵢ[ℝ] E) : roundChart p L 0 = p := by
  simp [roundChart,stereoInvFunAux]

lemma roundChart_first (p : E) (L : F →ₗᵢ[ℝ] E) :
    HasFDerivAt (roundChart p L) L.toContinuousLinearMap 0 := by
  have h : HasFDerivAt (stereoInvFunAux (-p)) (ContinuousLinearMap.id ℝ E)
      (L.toContinuousLinearMap 0) := by simpa using hasFDerivAt_stereoInvFunAux (-p)
  convert h.comp (0:F) L.toContinuousLinearMap.hasFDerivAt using 1
  · rfl
  · ext z
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LpProductLinearMap
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
section LpProductJets
variable {E F A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
lemma lpProductFunction_hasFDerivAt {f : E → A} {g : F → B}
    {x : WithLp 2 (E×F)} {Df : E →L[ℝ] A} {Dg : F →L[ℝ] B}
    (hf : HasFDerivAt f Df x.fst) (hg : HasFDerivAt g Dg x.snd) :
    HasFDerivAt (lpProductFunction f g) (lpProductLinearMap Df Dg) x := by
  have hp := HasFDerivAt.prodMap (x.fst,x.snd) hf hg
  have hi := hp.comp x (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap.hasFDerivAt
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.toContinuousLinearMap.hasFDerivAt.comp x hi
end LpProductJets
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_LpProductFunctionMetric
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E F A B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
lemma lpProductRoundChart_first (p : A) (q : B) (L : E →ₗᵢ[ℝ] A) (K : F →ₗᵢ[ℝ] B) :
    HasFDerivAt (lpProductFunction (roundChart p L) (roundChart q K))
      (lpProductIsometry L K).toContinuousLinearMap 0 := by
  exact lpProductFunction_hasFDerivAt (roundChart_first p L) (roundChart_first q K)
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
section GenericCoordinateHessian
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

local instance genericHessMapNorm_rc0b372_1 : NormedAddCommGroup (E →L[ℝ] V) := inferInstance
attribute [local instance] OAI.YauCounterexamples.genericHessMapSpace
local instance genericHessFormNorm_rc0b372_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance genericHessFormSpace_rc0b372_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance
lemma continuous_coordinateCovariantSecond
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ) {f : E → V}
    (hf : ContDiff ℝ ∞ f) : Continuous (coordinateCovariantSecond Γ f) := by
  apply Continuous.sub
  · exact (hf.fderiv_right (m:=(∞ : ℕ∞ω)) (by simp)).continuous_fderiv
      (by simp)
  · exact ((ContinuousLinearMap.compL ℝ E E V).continuous.comp
      (hf.continuous_fderiv (by simp))).clm_comp hΓ

end GenericCoordinateHessian

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

attribute [local instance] OAI.YauCounterexamples.prepDualNorm
attribute [local instance] OAI.YauCounterexamples.prepDualSpace
omit [FiniteDimensional ℝ E] in
lemma continuous_metricProfileTraceForm_comp {X : Type*} [TopologicalSpace X]
    {B H : X → CoordinateForm E} {a : X → E}
    (hB : Continuous B) (hH : Continuous H) (ha : Continuous a) :
    Continuous (fun x => metricProfileTraceForm (B x) (H x) (a x)) := by
  unfold metricProfileTraceForm
  exact (((hH.clm_apply ha).clm_apply ha).smul hB).add
    ((continuous_const.add ((hB.clm_apply ha).clm_apply ha)).smul hH)

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

lemma unitSphereFrame_orthogonal (p : Metric.sphere (0 : A) 1) (w : Euclidean n) :
    inner ℝ (p : A) (unitSphereFrame p w) = 0 := by
  have hh := ((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm w).property
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hh
  change inner ℝ (p : A) _ = 0
  rw [real_inner_comm]
  change inner ℝ _ (-(p : A)) = 0 at hh
  rw [inner_neg_right,neg_eq_zero] at hh
  exact hh

lemma unitSphere_chart_symm (p : Metric.sphere (0 : A) 1) :
    (fun y => ((chartAt (Euclidean n) p).symm y : A)) =
      roundChart (p : A) (unitSphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : A) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,unitSphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

end


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]

lemma unitSphereFrame_coordinates (p : Metric.sphere (0 : A) 1) (a : A) :
    unitSphereFrame (n:=n) p (unitSphereCoordinates (n:=n) p a) = unitSphereProjection p a := by
  change (((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm
      ((OrthonormalBasis.fromOrthogonalSpanSingleton n
        (ne_zero_of_mem_unit_sphere (-p))).repr ⟨unitSphereProjection p a,_⟩)) : A) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

lemma unitSphereCoordinates_inner (p : Metric.sphere (0 : A) 1) (a b : A) :
    inner ℝ (unitSphereCoordinates (n:=n) p a) (unitSphereCoordinates (n:=n) p b) =
      inner ℝ a b - inner ℝ (p : A) a * inner ℝ (p : A) b := by
  rw [← (unitSphereFrame (n:=n) p).inner_map_map,unitSphereFrame_coordinates,unitSphereFrame_coordinates]
  simp [unitSphereProjection,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    real_inner_comm a (p : A)]

lemma unitSphereFrame_inner (p : Metric.sphere (0 : A) 1) (a : A) (w : Euclidean n) :
    inner ℝ (unitSphereFrame (n:=n) p w) a = inner ℝ w (unitSphereCoordinates (n:=n) p a) := by
  rw [← (unitSphereFrame (n:=n) p).inner_map_map,unitSphereFrame_coordinates]
  have hh := unitSphereFrame_orthogonal p w
  rw [real_inner_comm] at hh
  simp [unitSphereProjection,inner_sub_right,inner_smul_right,hh]


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
lemma three_chart_symm (p : ThreeManifold) :
    threeImmersion ∘ (chartAt ThreeModel p).symm = threeChartMap p := by
  funext y
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · change ((chartAt (Euclidean 2) p.1).symm y.fst : Euclidean 3) = _
    exact congrFun (sphere_chart_symm p.1) y.fst
  · change ((chartAt (Euclidean 1) p.2).symm y.snd : ℂ) = _
    exact congrFun (unitSphere_chart_symm (n:=1) p.2) y.snd
attribute [local instance] OAI.YauCounterexamples.threeModelNormedSpace
local instance threeModelContinuousSMul_rc0b372_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma three_coordinate_embedding (p : ThreeManifold) (y v : ThreeModel) :
    mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion
      ((chartAt ThreeModel p).symm y)
      (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) (chartAt ThreeModel p).symm y v) =
        fderiv ℝ (threeChartMap p) y v := by
  have hy : y ∈ (chartAt ThreeModel p).target := by rw [three_chart_target]; trivial
  have hh := mfderiv_comp y
    (threeImmersion_smooth.mdifferentiable (by simp)).mdifferentiableAt
    ((contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (n := ∞) p) hy).mdifferentiableAt (by simp))
  have he := congrArg (fun L => L v) hh
  rw [mfderiv_eq_fderiv,three_chart_symm] at he
  exact he.symm
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
local instance threeChartContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul

attribute [local instance] OAI.YauCounterexamples.threeChartNormedSpace
lemma threeChartMetric_selfFlat (g : SmoothMetric ThreeModel ThreeManifold) (p : ThreeManifold) (y : ThreeModel) :
    selfMetricFlat (threeChartMetric g p) y = chartMetricForm g p y := by
  ext v w
  rw [selfMetricFlat_apply]
  rfl
lemma threeChartMetric_background (p : ThreeManifold) (y v w : ThreeModel) :
    selfMetricFlat (threeChartMetric threeBackgroundMetric p) y v w =
      inner ℝ (fderiv ℝ (threeChartMap p) y v) (fderiv ℝ (threeChartMap p) y w) := by
  rw [threeChartMetric_selfFlat,chartMetricForm_pairing]
  change (inner ℝ : ThreeAmbient → ThreeAmbient → ℝ) (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion _ _) _ = _
  exact congrArg₂ (inner ℝ : ThreeAmbient → ThreeAmbient → ℝ) (three_coordinate_embedding p y v) (three_coordinate_embedding p y w)
lemma threeChartMetric_background_zero (p : ThreeManifold) :
    selfMetricFlat (threeChartMetric threeBackgroundMetric p) 0 = (innerSL ℝ : ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ) := by
  ext v w
  have hh : fderiv ℝ (threeChartMap p) 0 = (threeFrame p).toContinuousLinearMap :=
    (lpProductRoundChart_first (p.1:Euclidean 3) (p.2:ℂ) (sphereFrame p.1) (unitSphereFrame (n:=1) p.2)).fderiv
  rw [threeChartMetric_background,hh]
  exact (threeFrame p).inner_map_map _ _
end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
local instance threeRadiusContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeRadiusEuclideanContinuousSMul (dimension : ℕ) : ContinuousSMul ℝ (Euclidean dimension) :=
  IsBoundedSMul.continuousSMul
local instance threeRadius_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩

attribute [local instance] OAI.YauCounterexamples.threeRadiusNormedSpace
lemma threeSphereMap_smooth (p : ThreeManifold) : ContDiff ℝ ∞ (threeSphereMap p) :=
  (roundChart_smooth _ _).comp (WithLp.fstL 2 ℝ (Euclidean 2) (Euclidean 1)).contDiff
lemma threeSphereMap_zero (p : ThreeManifold) : threeSphereMap p 0 = (p.1 : Euclidean 3) := by
  simp [threeSphereMap,Function.comp_apply,roundChart_zero]
lemma threeSphereMap_first (p : ThreeManifold) (v : ThreeModel) :
    fderiv ℝ (threeSphereMap p) 0 v = sphereFrame p.1 v.fst := by
  rw [threeSphereMap,directional_clm_comp_general _ ((roundChart_smooth _ _).differentiable (by simp))]
  change fderiv ℝ (roundChart (p.1:Euclidean 3) (sphereFrame p.1)) 0 v.fst = _
  rw [(roundChart_first _ _).fderiv]
  rfl
lemma threeSphereCoord_smooth (p : ThreeManifold) (i : Fin 3) :
    ContDiff ℝ ∞ (threeSphereCoord p i) := (innerSL ℝ (productAxis i)).contDiff.comp (threeSphereMap_smooth p)
lemma threeSphereCoord_zero (p : ThreeManifold) (i : Fin 3) :
    threeSphereCoord p i 0 = (p.1:Euclidean 3) i := by
  rw [threeSphereCoord,threeSphereMap_zero,productAxis_coord]
lemma threeSphereCoord_first (p : ThreeManifold) (i : Fin 3) (v : ThreeModel) :
    fderiv ℝ (threeSphereCoord p i) 0 v = inner ℝ (threeSphereDirection p i) v := by
  rw [show threeSphereCoord p i = fun y => (innerSL ℝ (productAxis i)) (threeSphereMap p y) from rfl]
  rw [fderiv_clm_comp_apply _ (threeSphereMap_smooth p),threeSphereMap_first]
  change inner ℝ (productAxis i) (unitSphereFrame (n:=2) p.1 v.fst)=_
  rw [real_inner_comm,unitSphereFrame_inner,real_inner_comm]
  simp [threeSphereDirection,WithLp.prod_inner_apply]
lemma threeRadiusSq_smooth (p : ThreeManifold) : ContDiff ℝ ∞ (threeRadiusSq p) :=
  ((threeSphereCoord_smooth p 0).pow 2).add ((threeSphereCoord_smooth p 1).pow 2)
lemma threeRadiusSq_zero (p : ThreeManifold) : threeRadiusSq p 0 =
    (p.1:Euclidean 3) 0^2+(p.1:Euclidean 3) 1^2 := by
  simp [threeRadiusSq,threeSphereCoord_zero]
lemma threeRadiusSq_first (p : ThreeManifold) (v : ThreeModel) :
    fderiv ℝ (threeRadiusSq p) 0 v =
      2*(p.1:Euclidean 3) 0*inner ℝ (threeSphereDirection p 0) v+
      2*(p.1:Euclidean 3) 1*inner ℝ (threeSphereDirection p 1) v := by
  have h0 := ((threeSphereCoord_smooth p 0).differentiable (by simp) (0:ThreeModel)).hasFDerivAt.pow 2
  have h1 := ((threeSphereCoord_smooth p 1).differentiable (by simp) (0:ThreeModel)).hasFDerivAt.pow 2
  have hh : HasFDerivAt (threeRadiusSq p) _ 0 := h0.add h1
  rw [hh.fderiv]
  simp [threeSphereCoord_zero,threeSphereCoord_first]

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ThreeLogNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
local instance threeLog_dimension_fact_rc0b372_1 (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
lemma threeSphereDirection_inner (p : ThreeManifold) (i j : Fin 3) :
    inner ℝ (threeSphereDirection p i) (threeSphereDirection p j) =
      (if i=j then 1 else 0)-(p.1:Euclidean 3) i*(p.1:Euclidean 3) j := by
  simp only [threeSphereDirection,WithLp.prod_inner_apply,
    inner_zero_left,add_zero,unitSphereCoordinates_inner]
  have hi : inner ℝ (p.1:Euclidean 3) (productAxis i) = (p.1:Euclidean 3) i := by rw [real_inner_comm,productAxis_coord]
  have hj : inner ℝ (p.1:Euclidean 3) (productAxis j) = (p.1:Euclidean 3) j := by rw [real_inner_comm,productAxis_coord]
  rw [hi,hj,productAxis_coord]
  simp [productAxis,PiLp.single_apply]
attribute [local instance] OAI.YauCounterexamples.threeLogNormedSpace
local instance threeLogContinuousSMul_rc0b372_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeLogEnvelope_first (p : ThreeManifold) (c : ℝ) (hq : threeRadiusSq p 0 ≠ 0) (v : ThreeModel) :
    fderiv ℝ (threeLogEnvelope p c) 0 v =
      (c/2)*(threeRadiusSq p 0)⁻¹*fderiv ℝ (threeRadiusSq p) 0 v := by
  change fderiv ℝ ((c/2) • (fun y => Real.log (threeRadiusSq p y))) 0 v = _
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply,smul_apply,smul_eq_mul]
  rw [scalarLog_first ((threeRadiusSq_smooth p).differentiable (by simp) 0) hq]
  ring

lemma threeLogEnvelope_first_axis (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) :
    fderiv ℝ (threeLogEnvelope p c) 0 = innerSL ℝ ((c/(p.1:Euclidean 3) 0) • threeSphereDirection p 0) := by
  have hq : threeRadiusSq p 0 ≠ 0 := by simp [threeRadiusSq_zero,hy,pow_ne_zero 2 hx]
  ext v
  rw [threeLogEnvelope_first p c hq,threeRadiusSq_first]
  simp only [threeRadiusSq_zero,hy,add_zero,mul_zero,zero_mul,innerSL_apply_apply,real_inner_smul_left]
  field_simp [hx]
  ring

lemma threeLogEnvelope_gradient (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) :
    coordinateMetricGradient (threeChartMetric threeBackgroundMetric p) (threeLogEnvelope p c) 0 =
      (c/(p.1:Euclidean 3) 0) • threeSphereDirection p 0 := by
  apply (selfMetricFlat_invertible (threeChartMetric threeBackgroundMetric p) 0).inverse_apply_eq.mpr
  rw [threeChartMetric_background_zero,threeLogEnvelope_first_axis p c hx hy]
lemma threeLogEnvelope_dual (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) :
    (InnerProductSpace.toDual ℝ ThreeModel).symm (fderiv ℝ (threeLogEnvelope p c) 0) =
      (c/(p.1:Euclidean 3) 0) • threeSphereDirection p 0 := by
  rw [LinearIsometryEquiv.symm_apply_eq,threeLogEnvelope_first_axis p c hx hy]
  rfl
lemma threeLogEnvelope_strict (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0)
    (hxlt : ((p.1:Euclidean 3) 0)^2<1) (hc : 0 < c) (hc1 : c<1) :
    coordinateMetricGradient (threeChartMetric threeBackgroundMetric p) (threeLogEnvelope p c) 0 ≠ 0 ∧
    actualProfileStrict (threeChartMetric threeBackgroundMetric p) (threeLogEnvelope p c) 0 := by
  have hv0 : threeSphereDirection p 0 ≠ 0 := by
    intro hh
    have hi:=threeSphereDirection_inner p 0 0
    simp only [hh,inner_zero_left,ite_true] at hi
    nlinarith
  have he : threeSphereDirection p 1 ≠ 0 := by
    intro hh
    have hi:=threeSphereDirection_inner p 1 1
    simp [hh,hy] at hi
  constructor
  · rw [threeLogEnvelope_gradient p c hx hy]
    exact smul_ne_zero (div_ne_zero (ne_of_gt hc) hx) hv0
  · rw [actualProfileStrict,quadraticPlaneStrict_iff_nonzero]
    refine ⟨threeSphereDirection p 1,he,?_,?_⟩
    · rw [threeLogEnvelope_dual p c hx hy,real_inner_smul_left,threeSphereDirection_inner]
      norm_num [hy]
    · rw [threeLogEnvelope_trace p c hx hy]
      have hcc : 0<1-c^2 := by nlinarith
      exact div_pos (mul_pos (mul_pos hc hcc) (sub_pos.mpr hxlt)) (sq_pos_of_ne_zero hx)
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_GlobalPrepDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma actualJet_eventuallyEq (g : SmoothMetric E E) {u v : E → ℝ} {x : E}
    (h : u =ᶠ[𝓝 x] v) :
    coordinateMetricGradient g u x = coordinateMetricGradient g v x ∧
    actualCoordinateHessian g u x = actualCoordinateHessian g v x ∧
    (actualProfileStrict g u x ↔ actualProfileStrict g v x) ∧
    (actualProfileFull g u x ↔ actualProfileFull g v x) := by
  have h₁ := h.fderiv_eq (𝕜:=ℝ)
  have h₂ := (h.fderiv (𝕜:=ℝ)).fderiv_eq (𝕜:=ℝ)
  have hg : coordinateMetricGradient g u x = coordinateMetricGradient g v x := by
    simp only [coordinateMetricGradient,h₁]
  have hh : actualCoordinateHessian g u x = actualCoordinateHessian g v x := by
    simp only [actualCoordinateHessian,coordinateCovariantSecond,h₁,h₂]
  exact ⟨hg,hh,by simp only [actualProfileStrict,actualProfileTraceForm,hg,hh,h₁],
    by simp only [actualProfileFull,actualProfileTraceForm,hg,hh,h₁]⟩

end
end YauCounterexamples

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

attribute [local instance] OAI.YauCounterexamples.jetDualNorm
attribute [local instance] OAI.YauCounterexamples.jetDualSpace
lemma contDiff_selfMetricFlat_inverse (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x
    (contDiff_selfMetricFlat g).contDiffAt

lemma continuous_metricJetMap (g : SmoothMetric E E) : Continuous (metricJetMap g) := by
  have hB : Continuous (fun z : MetricJet E => selfMetricFlat g z.1) :=
    (contDiff_selfMetricFlat g).continuous.comp continuous_fst
  have ha : Continuous (fun z : MetricJet E => (selfMetricFlat g z.1).inverse z.2.2) :=
    ((contDiff_selfMetricFlat_inverse g).continuous.comp continuous_fst).clm_apply continuous_snd.snd
  exact (continuous_metricProfileTraceForm_comp hB continuous_snd.fst ha).prodMk
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp continuous_snd.snd)

lemma isOpen_metricJetStrict (g : SmoothMetric E E) : IsOpen {z | metricJetStrict g z} := by
  have h : IsOpen {p : CoordinateForm E × E | p.2 ≠ 0 ∧ quadraticPlaneStrict p.1 p.2} := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    exact (continuous_snd.continuousAt.eventually_ne hp.1).and
      (quadraticPlaneStrict_eventually hp.1 hp.2)
  exact h.preimage (continuous_metricJetMap g)

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
section LocalLogExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
lemma exists_smooth_local_log {q : E → ℝ} (hq : ContDiff ℝ ∞ q) {x : E} (hx : q x ≠ 0) (c : ℝ) :
    ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      f =ᶠ[𝓝 x] (fun y => c*Real.log (q y)) := by
  have hO : {y | q y ≠ 0} ∈ 𝓝 x := hq.continuous.continuousAt.eventually_ne hx
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp hO
  let χ : ContDiffBump x := ⟨r/4,r/2,by positivity,by linarith⟩
  have hχ : tsupport χ ⊆ {y | q y ≠ 0} := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (half_lt_self hr)).trans hs
  let f : E → ℝ := fun y => χ y*(c*Real.log (q y))
  have hf : ContDiff ℝ ∞ f := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact χ.contDiffAt.mul (contDiffAt_const.mul (hq.contDiffAt.log (hχ hy)))
    · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp [f,hz]
  refine ⟨f,hf,χ.hasCompactSupport.mul_right,?_⟩
  filter_upwards [χ.eventuallyEq_one] with y hy
  simp [f,hy]

lemma actual_strict_region_open (g : SmoothMetric E E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    IsOpen {x | coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x} := by
  have hJ : Continuous (fun x => (x,actualCoordinateHessian g f x,fderiv ℝ f x)) :=
    continuous_id.prodMk ((continuous_coordinateCovariantSecond _
      (contDiff_metricChristoffel g).continuous hf).prodMk
      (hf.continuous_fderiv (by simp)))
  have hh := (isOpen_metricJetStrict g).preimage hJ
  change IsOpen {x | metricJetStrict g (x,actualCoordinateHessian g f x,fderiv ℝ f x)} at hh
  simpa only [metricJetStrict_actual] using hh
lemma exists_local_strict_ball (g : SmoothMetric E E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {x : E}
    (hx : coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x) :
    ∃ r>0, ∀ y ∈ closedBall x r,
      coordinateMetricGradient g f y ≠ 0 ∧ actualProfileStrict g f y := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp ((actual_strict_region_open g hf).mem_nhds hx)
  exact ⟨r/2,half_pos hr,fun y hy => hsub (closedBall_subset_ball (half_lt_self hr) hy)⟩
end LocalLogExtension

attribute [local instance] OAI.YauCounterexamples.threeLocalNormedSpace
local instance threeLocalContinuousSMul_rc0b372_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma exists_three_local_strict_profile (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0)
    (hxlt : ((p.1:Euclidean 3) 0)^2<1) (hc : 0 < c) (hc1 : c<1) :
    ∃ f : ThreeModel → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      f =ᶠ[𝓝 0] threeLogEnvelope p c ∧ ∃ r>0, ∀ y ∈ closedBall 0 r,
      coordinateMetricGradient (threeChartMetric threeBackgroundMetric p) f y ≠ 0 ∧
      actualProfileStrict (threeChartMetric threeBackgroundMetric p) f y := by
  have hq : threeRadiusSq p 0 ≠ 0 := by simp [threeRadiusSq_zero,hy,pow_ne_zero 2 hx]
  obtain ⟨f,hf,hfc,he⟩ := exists_smooth_local_log (threeRadiusSq_smooth p) hq (c/2)
  have he : f =ᶠ[𝓝 0] threeLogEnvelope p c := he
  have hj := actualJet_eventuallyEq (threeChartMetric threeBackgroundMetric p) he
  have hh := threeLogEnvelope_strict p c hx hy hxlt hc hc1
  have hf0 : coordinateMetricGradient (threeChartMetric threeBackgroundMetric p) f 0 ≠ 0 ∧
      actualProfileStrict (threeChartMetric threeBackgroundMetric p) f 0 := by
    rw [hj.1,hj.2.2.1]
    exact hh
  obtain ⟨r,hr,hstrict⟩ := exists_local_strict_ball _ hf hf0
  exact ⟨f,hf,hfc,he,r,hr,hstrict⟩
end


section
open Set Filter Function Manifold MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeProfilePoint_zero : (threeProfilePoint:Euclidean 3) 0 = 3/5 := rfl
lemma threeProfilePoint_one : (threeProfilePoint:Euclidean 3) 1 = 0 := rfl
lemma threeEnvelopeExponent_pos : 0<threeEnvelopeExponent := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
lemma threeEnvelopeExponent_lt : threeEnvelopeExponent<1 := by
  unfold threeEnvelopeExponent
  have h : 1<Real.sqrt 2 := by nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg 2]
  exact (inv_lt_one₀ (lt_trans zero_lt_one h)).mpr h

attribute [local instance] OAI.YauCounterexamples.threeCenterNormedSpace
local instance threeCenterContinuousSMul_rc0b372_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
theorem exists_three_profile_seed_oai :
    ∃ f : ThreeModel → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      f =ᶠ[𝓝 0] threeLogEnvelope threeProfileCenter threeEnvelopeExponent ∧
      ∃ r>0, ∀ y ∈ closedBall 0 r,
        coordinateMetricGradient (threeChartMetric threeBackgroundMetric threeProfileCenter) f y ≠ 0 ∧
        actualProfileStrict (threeChartMetric threeBackgroundMetric threeProfileCenter) f y := by
  apply exists_three_local_strict_profile threeProfileCenter threeEnvelopeExponent
  · norm_num [threeProfileCenter,threeProfilePoint_zero]
  · exact threeProfilePoint_one
  · norm_num [threeProfileCenter,threeProfilePoint_zero]
  · exact threeEnvelopeExponent_pos
  · exact threeEnvelopeExponent_lt

end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_three_profile_seed_oai := @OAI.YauCounterexamples.exists_three_profile_seed_oai
