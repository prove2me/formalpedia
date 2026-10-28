-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_three_robust_exhaustible_envelopes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:16:31.763696+00:00
-- url     : https://prove2.me/submissions/fb38df5c-ed01-43da-a04d-d26b073db0ff

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_exists_three_robust_seed

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

local instance genericHessMapNorm_r4d5172_1 : NormedAddCommGroup (E →L[ℝ] V) := inferInstance
attribute [local instance] OAI.YauCounterexamples.genericHessMapSpace
local instance genericHessFormNorm_r4d5172_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance genericHessFormSpace_r4d5172_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance
lemma continuous_coordinateCovariantSecond
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ) {f : E → V}
    (hf : ContDiff ℝ ∞ f) : Continuous (coordinateCovariantSecond Γ f) := by
  apply Continuous.sub
  · exact (hf.fderiv_right (m:=(∞ : ℕ∞ω)) (by simp)).continuous_fderiv
      (by simp)
  · exact ((ContinuousLinearMap.compL ℝ E E V).continuous.comp
      (hf.continuous_fderiv (by simp))).clm_comp hΓ

end GenericCoordinateHessian


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

end ScalarHessian

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ExistsCompactSignedEnvelope
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
lemma actualCoordinateHessian_const_mul (g : SmoothMetric E E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (s : ℝ) (x v w : E) :
    actualCoordinateHessian g (fun y => s*f y) x v w = s*actualCoordinateHessian g f x v w := by
  let L : ℝ →L[ℝ] ℝ := s • ContinuousLinearMap.id ℝ ℝ
  change actualCoordinateHessian g (fun y => L (f y)) x v w = _
  rw [actualCoordinateHessian_apply,fderiv_second_clm_comp_apply L hf,
    fderiv_clm_comp_apply L hf,actualCoordinateHessian_apply]
  simp only [L,smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
  ring

attribute [local instance] OAI.YauCounterexamples.perturbDualNorm
attribute [local instance] OAI.YauCounterexamples.perturbDualSpace
attribute [local instance] OAI.YauCounterexamples.perturbFormNorm
local instance perturbFormSpace_r4d5172_1 : NormedSpace ℝ (CoordinateForm E) := inferInstance
theorem exists_compact_strict_perturbation (g : SmoothMetric E E) {f h : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) {K : Set E} (hK : IsCompact K)
    (hstrict : ∀ x ∈ K, coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x) :
    ∃ ε>0, ∀ s : ℝ, |s|<ε → ∀ x ∈ K,
      coordinateMetricGradient g (fun y => f y+s*h y) x ≠ 0 ∧
      actualProfileStrict g (fun y => f y+s*h y) x := by
  let J : E × ℝ → MetricJet E := fun z =>
    (z.1,actualCoordinateHessian g f z.1+z.2 • actualCoordinateHessian g h z.1,
      fderiv ℝ f z.1+z.2 • fderiv ℝ h z.1)
  have hHf : Continuous (actualCoordinateHessian g f) :=
    continuous_coordinateCovariantSecond _ (contDiff_metricChristoffel g).continuous hf
  have hHh : Continuous (actualCoordinateHessian g h) :=
    continuous_coordinateCovariantSecond _ (contDiff_metricChristoffel g).continuous hh
  have hJ : Continuous J := continuous_fst.prodMk
    (((hHf.comp continuous_fst).add (continuous_snd.smul (hHh.comp continuous_fst))).prodMk
      (((hf.continuous_fderiv (by simp)).comp continuous_fst).add
        (continuous_snd.smul ((hh.continuous_fderiv (by simp)).comp continuous_fst))))
  have hsub : K ×ˢ ({0}:Set ℝ) ⊆ J ⁻¹' {z | metricJetStrict g z} := by
    rintro ⟨x,s⟩ ⟨hx,hs⟩
    simp only [mem_singleton_iff] at hs
    subst s
    simpa only [mem_preimage,mem_ofPred_eq,J,zero_smul,add_zero,metricJetStrict_actual] using hstrict x hx
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma hK isCompact_singleton
    ((isOpen_metricJetStrict g).preimage hJ) hsub
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V (mem_singleton 0)))
  refine ⟨ε,hε,?_⟩
  intro s hs x hx
  have hj := hUV (show (x,s) ∈ U ×ˢ V from
    ⟨hKU hx,hεV (by simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs] using hs)⟩)
  have heH : actualCoordinateHessian g (fun y => f y+s*h y) x =
      actualCoordinateHessian g f x+s • actualCoordinateHessian g h x := by
    ext v w
    rw [actualCoordinateHessian_add g hf (contDiff_const.mul hh),
      actualCoordinateHessian_const_mul g hh]
    rfl
  have heD : fderiv ℝ (fun y => f y+s*h y) x = fderiv ℝ f x+s • fderiv ℝ h x := by
    rw [fderiv_fun_add (hf.differentiable (by simp) x)
      ((contDiff_const.mul hh).differentiable (by simp) x),
      fderiv_const_mul (hh.differentiable (by simp) x)]
  rw [← metricJetStrict_actual,heH,heD]
  exact hj
end


open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ExistsExhaustibleSignedEnvelope
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_exhaustible_signed_envelope (g : SmoothMetric E E) {f l : E → ℝ}
    (hf : ContDiff ℝ ∞ f) {R : ℝ} (hR : 0<R)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hbR : b<R/2) (C : ℝ)
    (hmin : ∀ x, C+1≤l x) (heq : ∀ x ∈ closedBall 0 R, f x=l x)
    (hstrict : ∀ x ∈ closedBall 0 R,
      coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x) :
    ∃ δ>0, δ≤1/2 ∧ ∃ φ : E → ℝ, ContDiff ℝ ∞ φ ∧
      HasCompactSupport (fun x => φ x-C) ∧
      tsupport (fun x => φ x-C) ⊆ closedBall 0 (3*R/4) ∧
      (∀ x ∈ closedBall 0 (b),
        coordinateMetricGradient g φ x ≠ 0 ∧ actualProfileStrict g φ x) ∧
      (∀ x ∈ closedBall 0 a, φ x=l x+δ) ∧
      (∀ x ∉ closedBall 0 (b), φ x≤l x-δ) := by
  let β : ContDiffBump (0:E) := ⟨a,b,ha,hab⟩
  let χ : ContDiffBump (0:E) := ⟨R/2,3*R/4,by positivity,by linarith⟩
  let h : E → ℝ := fun x => 2*β x-1
  have hh : ContDiff ℝ ∞ h := (contDiff_const.mul β.contDiff).sub contDiff_const
  obtain ⟨ε,hε,hstable⟩ := exists_compact_strict_perturbation g hf hh
    (isCompact_closedBall 0 (b)) (fun x hx => hstrict x
      (closedBall_subset_closedBall (by linarith) hx))
  let δ := min (ε/2) (1/2)
  have hδ : 0<δ := lt_min (half_pos hε) (by norm_num)
  have hδε : |δ|<ε := by rw [abs_of_pos hδ]; exact (min_le_left _ _).trans_lt (half_lt_self hε)
  have hδ1 : δ≤1/2 := min_le_right _ _
  let φ : E → ℝ := fun x => C+χ x*(f x-δ-C)+2*δ*β x
  have hφ : ContDiff ℝ ∞ φ :=
    (contDiff_const.add (χ.contDiff.mul ((hf.sub contDiff_const).sub contDiff_const))).add
      (contDiff_const.mul β.contDiff)
  have hcover : tsupport (fun x => φ x-C) ⊆ closedBall 0 (3*R/4) := by
    apply closure_minimal ?_ isClosed_closedBall
    intro x hx
    by_contra hh
    have hχ : χ x=0 := χ.zero_of_le_dist (by
      have hn : 3*R/4 < dist x 0 := by simpa only [mem_closedBall,not_le] using hh
      exact hn.le)
    have hβ : β x=0 := β.zero_of_le_dist (by
      have hn : 3*R/4 < dist x 0 := by simpa only [mem_closedBall,not_le] using hh
      dsimp [β]; linarith)
    exact hx (by simp [φ,hχ,hβ])
  refine ⟨δ,hδ,hδ1,φ,hφ,?_,hcover,?_,?_,?_⟩
  · exact (isCompact_closedBall 0 (3*R/4)).of_isClosed_subset (isClosed_tsupport _) hcover
  · intro x hx
    have heχ := χ.eventuallyEq_one_of_mem_ball (show x ∈ ball 0 χ.rIn from
      closedBall_subset_ball (by dsimp [χ]; linarith) hx)
    have he : φ =ᶠ[𝓝 x] (fun y => f y+δ*h y) := by
      filter_upwards [heχ] with y hy
      dsimp [φ,h]
      change χ y=1 at hy
      rw [hy]
      ring
    have hj := actualJet_eventuallyEq g he
    rw [hj.1,hj.2.2.1]
    exact hstable δ hδε x hx
  · intro x hx
    have hβ := β.one_of_mem_closedBall hx
    have hχ := χ.one_of_mem_closedBall (closedBall_subset_closedBall (by dsimp [χ]; linarith) hx)
    have he := heq x (closedBall_subset_closedBall (by linarith) hx)
    dsimp [φ]
    rw [hβ,hχ,he]
    ring
  · intro x hx
    have hd : b < dist x 0 := by simpa only [mem_closedBall,not_le] using hx
    have hβ : β x=0 := β.zero_of_le_dist (by dsimp [β]; linarith)
    have hlow : C≤l x-δ := by have hm:=hmin x; linarith
    dsimp [φ]
    rw [hβ,mul_zero,add_zero]
    by_cases hz : χ x=0
    · simpa [hz] using hlow
    · have hmem : x ∈ ball 0 χ.rOut := by rwa [←χ.support_eq]
      have he := heq x (ball_subset_closedBall.trans
        (closedBall_subset_closedBall (by dsimp [χ]; linarith)) hmem)
      rw [he]
      have hc := χ.le_one (x:=x)
      have hn := χ.nonneg (x:=x)
      nlinarith
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
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

attribute [local instance] OAI.YauCounterexamples.threeRobustNormedSpace
local instance threeRobustContinuousSMul_r4d5172_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
theorem exists_three_robust_exhaustible_envelopes_oai :
    ∃ C R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
      ∀ g ∈ N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
      ∃ δ>0, δ≤1/2 ∧ ∃ φ : NormalWaveSpace → ℝ,
        ContDiff ℝ ∞ φ ∧ HasCompactSupport (fun y => φ y-C) ∧
        tsupport (fun y => φ y-C) ⊆ closedBall 0 (3*R/4) ∧
        (∀ y ∈ closedBall 0 b,
          coordinateMetricGradient (threeNormalMetricOf g) φ y ≠ 0 ∧
          actualProfileStrict (threeNormalMetricOf g) φ y) ∧
        (∀ y ∈ closedBall 0 a, φ y=threeGlobalLog (threeNormalInv y)+δ) ∧
        (∀ y ∉ closedBall 0 b, φ y≤threeGlobalLog (threeNormalInv y)-δ) ∧
        (∀ p, C≤threeGlobalLog p-δ) := by
  obtain ⟨C,R,hR,hclean,F,hF,he,hmin,N,hN,h0N,hs⟩ := exists_three_robust_seed
  refine ⟨C,R,hR,hclean,N,hN,h0N,?_⟩
  intro g hg a b ha hab hb
  obtain ⟨δ,hδ,hδ1,φ,hφ,hφc,hφs,hstrict,hin,hout⟩ :=
    exists_exhaustible_signed_envelope (threeNormalMetricOf g) hF hR a b ha hab hb C
      (fun y => hmin (threeNormalInv y)) he (hs g hg)
  exact ⟨δ,hδ,hδ1,φ,hφ,hφc,hφs,hstrict,hin,hout,fun p => by linarith [hmin p]⟩
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_three_robust_exhaustible_envelopes_oai := @OAI.YauCounterexamples.exists_three_robust_exhaustible_envelopes_oai
