-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_three_robust_global_profile_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:16:32.759952+00:00
-- url     : https://prove2.me/submissions/6e6e8af9-ae97-4318-aec1-d4b0cffdd3da

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_actual_metric_profile_cycle
import Theorems.Thm_OAI_YauCounterexamples_exists_three_robust_exhaustible_envelopes

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

attribute [local instance] OAI.YauCounterexamples.actualDualNorm
attribute [local instance] OAI.YauCounterexamples.actualDualSpace
lemma contDiff_coordinateMetricGradient (g : SmoothMetric E E) {ψ : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (coordinateMetricGradient g ψ) := by
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x
      (contDiff_selfMetricFlat g).contDiffAt
  exact hGi.clm_apply (hψ.fderiv_right (m:=∞) (by simp))


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

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_nonneg (g : SmoothMetric E E) (x v : E) :
    0 ≤ actualCoordinateNorm g x v := Real.sqrt_nonneg _

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_pos (g : SmoothMetric E E) (x : E) {v : E} (hv : v ≠ 0) :
    0 < actualCoordinateNorm g x v := Real.sqrt_pos.mpr (selfMetricFlat_pos g x hv)

attribute [local instance] OAI.YauCounterexamples.globalPrepDualNorm
attribute [local instance] OAI.YauCounterexamples.globalPrepDualSpace
local instance globalPrepInvNorm_r0c443a_1 : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance
local instance globalPrepInvSpace_r0c443a_1 : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma continuous_actualCoordinateNorm (g : SmoothMetric E E) {v : E → E}
    (hv : Continuous v) : Continuous (fun x => actualCoordinateNorm g x (v x)) :=
  (((contDiff_selfMetricFlat g).continuous.clm_apply hv).clm_apply hv).sqrt

lemma continuous_actualProfileSpeed (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) : Continuous (actualProfileSpeed g u) :=
  continuous_actualCoordinateNorm g (contDiff_coordinateMetricGradient g hu).continuous

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_FixedRadialChoice
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff

lemma FixedRadialChoice.fraction_pos (D : FixedRadialChoice) : 0 < D.fraction := by
  dsimp [FixedRadialChoice.fraction]
  exact sq_pos_of_pos (by linarith [D.radius_pos])

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_ActualProfileSpeedNonneg
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace YauCounterexamples
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma actualProfileSpeed_nonneg (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    0 ≤ actualProfileSpeed g u x := actualCoordinateNorm_nonneg g x _

lemma integrableOn_actualProfileSpeed (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {Ω : Set E} (hΩ : IsCompact (closure Ω))
    (μ : Measure E) [IsLocallyFiniteMeasure μ] : IntegrableOn (actualProfileSpeed g u) Ω μ :=
  ((continuous_actualProfileSpeed g hu).continuousOn.integrableOn_compact hΩ).mono_set subset_closure

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ActualProfileCycleGain
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set MeasureTheory Filter
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

lemma actualProfileCycleGain_pos : 0 < actualProfileCycleGain := by
  unfold actualProfileCycleGain
  exact div_pos (mul_pos fixedRadialChoice.fraction_pos fixedRadialChoice.gain_pos) (by norm_num)



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

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ActualProfileMassPos
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace YauCounterexamples
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma actualProfileMass_pos (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {Ω : Set E} (hΩm : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (ha : ∀ x ∈ Ω, coordinateMetricGradient g u x ≠ 0)
    (μ : Measure E) [IsLocallyFiniteMeasure μ] (hμ : μ Ω ≠ 0) :
    0 < actualProfileMass g u μ Ω := by
  apply (integral_pos_iff_support_of_nonneg (actualProfileSpeed_nonneg g u)
    (integrableOn_actualProfileSpeed g hu hΩc μ)).mpr
  have hsub : Ω ⊆ Function.support (actualProfileSpeed g u) := by
    intro x hx
    exact ne_of_gt (actualCoordinateNorm_pos g x (ha x hx))
  have hh : 0 < (μ.restrict Ω) Ω := by simpa only [Measure.restrict_apply hΩm,inter_self] using pos_iff_ne_zero.mpr hμ
  exact hh.trans_le (measure_mono hsub)

theorem actual_metric_profile_iterate (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g u x ≠ 0)
    (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g u x)
    (μ : Measure E) [IsLocallyFiniteMeasure μ] (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport (fun x => v x-u x) ∧
      tsupport (fun x => v x-u x) ⊆ Ω ∧ (∀ x, |v x-u x| < ε) ∧
      (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x) ∧
      (1+actualProfileCycleGain)^n*actualProfileMass g u μ Ω ≤ actualProfileMass g v μ Ω := by
  induction n generalizing ε with
  | zero =>
    refine ⟨u,hu,?_,?_,?_,fun x hx => ⟨ha x hx,hstrict x hx⟩,?_⟩
    · dsimp [HasCompactSupport]; simp
    · simp
    · simpa using (fun _ : E => hε)
    · simp
  | succ n ih =>
    obtain ⟨v,hv,hvc,hvs,hv0,hvp,hvm⟩ := ih (half_pos hε)
    obtain ⟨w,hw,hwc,hws,hw0,hwp,hwm⟩ := actual_metric_profile_cycle hdim g hv hΩ hΩc
      (fun x hx => (hvp x hx).1) (fun x hx => (hvp x hx).2) μ (half_pos hε)
    refine ⟨w,hw,?_,?_,?_,hwp,?_⟩
    · have he : ((fun x => w x-v x)+(fun x => v x-u x)) = (fun x => w x-u x) := by
        funext x; dsimp; ring
      exact he ▸ hwc.add hvc
    · have hs := (tsupport_add (fun x => w x-v x) (fun x => v x-u x)).trans (union_subset hws hvs)
      simpa only [Pi.add_apply,sub_add_sub_cancel] using hs
    · intro x
      calc |w x-u x| = |(w x-v x)+(v x-u x)| := by congr 1; ring
        _ ≤ |w x-v x|+|v x-u x| := abs_add_le _ _
        _ < ε/2+ε/2 := add_lt_add (hw0 x) (hv0 x)
        _ = ε := by ring
    · have hh := mul_le_mul_of_nonneg_left hvm (show 0 ≤ 1+actualProfileCycleGain by linarith [actualProfileCycleGain_pos])
      rw [pow_succ]
      nlinarith only [hh,hwm]

theorem actual_metric_profile_amplification (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g u x ≠ 0)
    (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g u x)
    (μ : Measure E) [IsLocallyFiniteMeasure μ] (hμ : μ Ω ≠ 0)
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport (fun x => v x-u x) ∧
      tsupport (fun x => v x-u x) ⊆ Ω ∧ (∀ x, |v x-u x| < ε) ∧
      (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x) ∧
      T < actualProfileMass g v μ Ω := by
  have hM := actualProfileMass_pos g hu hΩ.measurableSet hΩc
    (fun x hx => ha x (subset_closure hx)) μ hμ
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (T/actualProfileMass g u μ Ω)
    (show 1 < 1+actualProfileCycleGain by linarith [actualProfileCycleGain_pos])
  obtain ⟨v,hv,hvc,hvs,hv0,hvp,hvm⟩ := actual_metric_profile_iterate hdim g hu hΩ hΩc ha hstrict μ n hε
  exact ⟨v,hv,hvc,hvs,hv0,hvp,((div_lt_iff₀ hM).mp hn).trans_le hvm⟩

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_CompactRegularLevelIntrinsicFinite
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter MeasureTheory BoxIntegral
open scoped Topology ContDiff

lemma box_Ioo_closure (I : Box (Fin 3)) : closure (Box.Ioo I) = Box.Icc I := by
  rw [Box.Icc_def,←Set.pi_univ_Icc]
  change closure (Set.pi univ (fun i => Set.Ioo (I.lower i) (I.upper i))) =
    Set.pi univ (fun i => Set.Icc (I.lower i) (I.upper i))
  rw [closure_pi_set]
  congr 1
  funext i
  exact closure_Ioo (I.lower_lt_upper i).ne

lemma normal_box_closure (I : Box (Fin 3)) :
    closure (normalWaveEquiv '' Box.Ioo I) = normalWaveEquiv '' Box.Icc I := by
  have he := normalWaveEquiv.toHomeomorph.image_closure (Box.Ioo I)
  change normalWaveEquiv '' closure (Box.Ioo I) = closure (normalWaveEquiv '' Box.Ioo I) at he
  rw [←he,box_Ioo_closure]

lemma normal_box_open (I : Box (Fin 3)) : IsOpen (normalWaveEquiv '' Box.Ioo I) :=
  normalWaveEquiv.toHomeomorph.isOpenMap _ (isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo))

lemma normal_box_measure_ne_zero (I : Box (Fin 3)) :
    normalCoordinateVolume (normalWaveEquiv '' Box.Ioo I) ≠ 0 := by
  rw [normalCoordinateVolume,Measure.map_apply normalWaveEquiv.continuous.measurable
    (normal_box_open I).measurableSet,Set.preimage_image_eq _ normalWaveEquiv.injective]
  have hv : 0 < (volume (Box.Ioo I)).toReal := by
    rw [measure_congr I.Ioo_ae_eq_Icc,←measure_congr I.coe_ae_eq_Icc,Box.volume_apply']
    exact Finset.prod_pos (fun i _ => sub_pos.mpr (I.lower_lt_upper i))
  intro h
  rw [h,ENNReal.toReal_zero] at hv
  exact lt_irrefl _ hv

lemma profileSpeed_le_frequencyScale (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) :
    actualProfileSpeed g φ x ≤ profileFrequencyScale g φ x := by
  apply Real.sqrt_le_sqrt
  change selfMetricFlat g x (coordinateMetricGradient g φ x) (coordinateMetricGradient g φ x) ≤
    1+selfMetricFlat g x (coordinateMetricGradient g φ x) (coordinateMetricGradient g φ x)
  linarith

lemma actual_profile_mass_le_box_frequency_integral
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace) {φ : NormalWaveSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (I : Box (Fin 3)) :
    actualProfileMass g φ normalCoordinateVolume (normalWaveEquiv '' Box.Ioo I) ≤
      ∫ x in Box.Icc I, profileFrequencyScale g φ (normalWaveEquiv x) := by
  have he := normalWaveEquiv.toHomeomorph.measurableEmbedding.setIntegral_map
    (μ := volume) (actualProfileSpeed g φ) (normalWaveEquiv '' Box.Ioo I)
  change (∫ x in normalWaveEquiv '' Box.Ioo I, actualProfileSpeed g φ x ∂Measure.map normalWaveEquiv volume) =
    (∫ x in normalWaveEquiv ⁻¹' (normalWaveEquiv '' Box.Ioo I), actualProfileSpeed g φ (normalWaveEquiv x)) at he
  rw [actualProfileMass,normalCoordinateVolume,he,Set.preimage_image_eq _ normalWaveEquiv.injective]
  rw [setIntegral_congr_set I.Ioo_ae_eq_Icc]
  apply setIntegral_mono_on
    (((continuous_actualProfileSpeed g hφ).comp normalWaveEquiv.continuous).continuousOn.integrableOn_compact I.isCompact_Icc)
    ((Real.continuous_sqrt.comp ((continuous_profileFrequencyEnergy g hφ).comp normalWaveEquiv.continuous)).continuousOn.integrableOn_compact I.isCompact_Icc)
    I.measurableSet_Icc
  exact fun x _ => profileSpeed_le_frequencyScale g φ _

theorem exists_box_amplified_profile (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (I : Box (Fin 3)) {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (ha : ∀ x ∈ normalWaveEquiv '' Box.Icc I, coordinateMetricGradient g φ x ≠ 0)
    (hstrict : ∀ x ∈ normalWaveEquiv '' Box.Icc I, actualProfileStrict g φ x)
    (T : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ψ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ ψ ∧
      HasCompactSupport (fun x => ψ x-φ x) ∧
      tsupport (fun x => ψ x-φ x) ⊆ normalWaveEquiv '' Box.Ioo I ∧
      (∀ x, |ψ x-φ x| < η) ∧
      (∀ x ∈ normalWaveEquiv '' Box.Icc I,
        coordinateMetricGradient g ψ x ≠ 0 ∧ actualProfileStrict g ψ x) ∧
      T < ∫ x in Box.Icc I, profileFrequencyScale g ψ (normalWaveEquiv x) := by
  have hd : Module.finrank ℝ NormalWaveSpace = 3 := by simp [NormalWaveSpace]
  have hc : IsCompact (closure (normalWaveEquiv '' Box.Ioo I)) := by
    rw [normal_box_closure]
    exact I.isCompact_Icc.image normalWaveEquiv.continuous
  obtain ⟨ψ,hψ,hψc,hψs,hψ0,hψp,hψmass⟩ := actual_metric_profile_amplification hd g hφ
    (normal_box_open I) hc (fun x hx => ha x (by simpa only [normal_box_closure] using hx))
    (fun x hx => hstrict x (by simpa only [normal_box_closure] using hx))
    normalCoordinateVolume (normal_box_measure_ne_zero I) T hη
  refine ⟨ψ,hψ,hψc,hψs,hψ0,?_,hψmass.trans_le (actual_profile_mass_le_box_frequency_integral g hψ I)⟩
  intro x hx
  exact hψp x (by simpa only [normal_box_closure] using hx)

end



open Set Filter Metric Manifold MeasureTheory Bundle
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Function Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ExistsGlobalBoxAmplifiedProfile
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma profile_eq_germ_of_not_tsupport {φ ψ : E → ℝ} {x : E}
    (hx : x ∉ tsupport (fun y => ψ y - φ y)) : ψ =ᶠ[𝓝 x] φ := by
  have h := notMem_tsupport_iff_eventuallyEq.mp hx
  filter_upwards [h] with y hy
  exact sub_eq_zero.mp hy

end


open Set Filter MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


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
lemma threeNormalGlue_chart (C : ℝ) (f : NormalWaveSpace → ℝ) :
    threeNormalGlue C f ∘ threeNormalInv=f := by
  funext y
  dsimp [threeNormalGlue,threeNormalInv]
  rw [manifoldChartPush_apply _ _ (by rw [three_chart_target]; trivial)]
  simp
attribute [local instance] OAI.YauCounterexamples.threeNormalEnvelopeNormedSpace
local instance threeNormalEnvelopeContinuousSMul_r0c443a_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeNormalGlue_smooth (C : ℝ) {f : NormalWaveSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport (fun y => f y-C)) :
    ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeNormalGlue C f) := by
  exact contMDiff_const.add (contMDiff_manifoldChartPush _
    ((hf.sub contDiff_const).comp threeNormalEquiv.symm.contDiff)
    (hc.comp_homeomorph threeNormalEquiv.symm.toHomeomorph)
    (by rw [three_chart_target]; exact subset_univ _))
lemma threeNormalGlue_tsupport (C : ℝ) {f : NormalWaveSpace → ℝ}
    (hc : HasCompactSupport (fun y => f y-C)) {K : Set NormalWaveSpace}
    (hK : tsupport (fun y => f y-C) ⊆ K) :
    tsupport (fun p => threeNormalGlue C f p-C) ⊆ threeNormalInv '' K := by
  have he : (fun p => threeNormalGlue C f p-C)=
      manifoldChartPush threeProfileCenter ((fun y => f y-C) ∘ threeNormalEquiv.symm) := by
    funext p; simp [threeNormalGlue]
  rw [he]
  intro p hp
  obtain ⟨y,hy,rfl⟩ := manifoldChartPush_tsupport _
    (hc.comp_homeomorph threeNormalEquiv.symm.toHomeomorph)
    (by rw [three_chart_target]; exact subset_univ _) hp
  rw [tsupport_comp_eq_preimage _ threeNormalEquiv.symm.toHomeomorph] at hy
  refine ⟨threeNormalEquiv.symm y,hK hy,?_⟩
  simp [threeNormalInv]
lemma threeNormalGlue_exterior (C δ : ℝ) {f l : NormalWaveSpace → ℝ}
    {L : ThreeManifold → ℝ} {K : Set NormalWaveSpace}
    (heL : l=L ∘ threeNormalInv) (hmin : ∀ p, C≤L p-δ)
    (hext : ∀ y ∉ K, f y≤l y-δ) :
    ∀ p ∉ threeNormalInv '' K, threeNormalGlue C f p≤L p-δ := by
  intro p hp
  by_cases hs : p ∈ (chartAt ThreeModel threeProfileCenter).source
  · let y := threeNormalEquiv.symm (chartAt ThreeModel threeProfileCenter p)
    have hey : threeNormalInv y=p := by simp [threeNormalInv,y,(chartAt ThreeModel threeProfileCenter).left_inv hs]
    have hy : y ∉ K := fun hh => hp ⟨y,hh,hey⟩
    have hec := congrFun (threeNormalGlue_chart C f) y
    have hec' : threeNormalGlue C f p=f y := by
      simpa only [Function.comp_apply,hey] using hec
    rw [hec']
    simpa only [heL,Function.comp_apply,hey] using hext y hy
  · simpa [threeNormalGlue,manifoldChartPush,Set.indicator_of_notMem hs] using hmin p

end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

attribute [local instance] OAI.YauCounterexamples.threeRobustProfileNormedSpace
local instance threeRobustProfileContinuousSMul_r0c443a_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
theorem exists_three_robust_global_profile_family_oai :
    ∃ C R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
      ∀ g ∈ N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
      ∃ δ>0, ∃ I : Box (Fin 3),
        normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
        ∀ T : ℝ, ∃ Φ : ThreeManifold → ℝ,
          ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ Φ ∧
          ContDiff ℝ ∞ (Φ ∘ threeNormalInv) ∧
          tsupport (fun p => Φ p-C) ⊆ threeNormalInv '' closedBall 0 (3*R/4) ∧
          (∀ y ∈ closedBall 0 b,
            coordinateMetricGradient (threeNormalMetricOf g) (Φ ∘ threeNormalInv) y ≠ 0 ∧
            actualProfileStrict (threeNormalMetricOf g) (Φ ∘ threeNormalInv) y) ∧
          (∀ y ∈ closedBall 0 a,
            threeGlobalLog (threeNormalInv y)+δ/2 < Φ (threeNormalInv y)) ∧
          (∀ p ∉ threeNormalInv '' closedBall 0 b, Φ p≤threeGlobalLog p-δ) ∧
          T < ∫ x in Box.Icc I, profileFrequencyScale (threeNormalMetricOf g)
            (Φ ∘ threeNormalInv) (normalWaveEquiv x) := by
  obtain ⟨C,R,hR,hclean,N,hN,h0N,hprod⟩ := exists_three_robust_exhaustible_envelopes
  refine ⟨C,R,hR,hclean,N,hN,h0N,?_⟩
  intro g hg a b ha hab hbR
  obtain ⟨δ,hδ,hδ1,φ,hφ,hφc,hφs,hstrict,hin,hout,hmin⟩ := hprod g hg a b ha hab hbR
  have hne : (normalWaveEquiv ⁻¹' ball (0:NormalWaveSpace) a).Nonempty := by
    refine ⟨0,?_⟩
    simpa only [mem_preimage,map_zero,mem_ball,dist_self] using (show 0<a from ha)
  obtain ⟨I,hI⟩ := exists_box_Icc_subset_open
    (isOpen_ball.preimage normalWaveEquiv.continuous) hne
  have hIs : normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a := by
    rintro y ⟨x,hx,rfl⟩
    exact ball_subset_closedBall (hI hx)
  have hIK : normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 b :=
    hIs.trans (closedBall_subset_closedBall (by linarith))
  refine ⟨δ,hδ,I,hIs,?_⟩
  intro T
  obtain ⟨ψ,hψ,hψc,hψs,hclose,hinside,hmass⟩ := exists_box_amplified_profile
    (threeNormalMetricOf g) I hφ (fun y hy => (hstrict y (hIK hy)).1)
    (fun y hy => (hstrict y (hIK hy)).2) T (half_pos hδ)
  have hd : (fun y => ψ y-C)=(fun y => ψ y-φ y)+(fun y => φ y-C) := by
    funext y; simp
  have hc : HasCompactSupport (fun y => ψ y-C) := hd ▸ hψc.add hφc
  have hsupport : tsupport (fun y => ψ y-C) ⊆ closedBall 0 (3*R/4) := by
    rw [hd]
    apply (tsupport_add _ _).trans (union_subset ?_ hφs)
    exact hψs.trans ((image_mono I.Ioo_subset_Icc).trans
      (hIs.trans (closedBall_subset_closedBall (by linarith))))
  have heoff (y : NormalWaveSpace) (hy : y ∉ normalWaveEquiv '' Box.Icc I) :
      ψ =ᶠ[𝓝 y] φ := by
    apply profile_eq_germ_of_not_tsupport
    exact fun hs => hy ((image_mono I.Ioo_subset_Icc) (hψs hs))
  have hψstrict : ∀ y ∈ closedBall 0 b,
      coordinateMetricGradient (threeNormalMetricOf g) ψ y ≠ 0 ∧ actualProfileStrict (threeNormalMetricOf g) ψ y := by
    intro y hy
    by_cases hz : y ∈ normalWaveEquiv '' Box.Icc I
    · exact hinside y hz
    · have hj := actualJet_eventuallyEq (threeNormalMetricOf g) (heoff y hz)
      rw [hj.1,hj.2.2.1]
      exact hstrict y hy
  have hψout : ∀ y ∉ closedBall 0 b, ψ y≤threeGlobalLog (threeNormalInv y)-δ := by
    intro y hy
    have hz : y ∉ normalWaveEquiv '' Box.Icc I := fun hh => hy (hIK hh)
    rw [(heoff y hz).self_of_nhds]
    exact hout y hy
  let Φ := threeNormalGlue C ψ
  have hchart : Φ ∘ threeNormalInv=ψ := threeNormalGlue_chart C ψ
  refine ⟨Φ,threeNormalGlue_smooth C hψ hc,?_,threeNormalGlue_tsupport C hc hsupport,?_,?_,?_,?_⟩
  · rw [hchart]; exact hψ
  · rw [hchart]; exact hψstrict
  · intro y hy
    have hcl := (abs_lt.mp (hclose y)).1
    have hbase := hin y hy
    have he : Φ (threeNormalInv y)=ψ y := congrFun hchart y
    rw [he]
    linarith
  · exact threeNormalGlue_exterior C δ rfl hmin hψout
  · rw [hchart]; exact hmass

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_three_robust_global_profile_family_oai := @OAI.YauCounterexamples.exists_three_robust_global_profile_family_oai
