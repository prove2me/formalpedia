-- Prove2me | solution 1 for OAI.YauCounterexamples.actual_metric_profile_cycle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:57:20.061211+00:00
-- url     : https://prove2.me/submissions/bfc2bd3c-6305-457b-9363-49ae81c5a8bd

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_actual_metric_radial_finite
import Theorems.Thm_OAI_YauCounterexamples_actual_preparation_on_compact_patch
import Theorems.Thm_OAI_YauCounterexamples_exists_actual_preparation_neighborhood

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
theorem isOpen_quadraticPlaneFull : IsOpen {p : CoordinateForm E × E | quadraticPlaneFull p.1 p.2} := by
  let S : Set E := sphere 0 1
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  let B : Set ((CoordinateForm E × E) × S) := {p | inner ℝ p.1.2 (p.2 : E) = 0 ∧
    p.1.1 p.2 p.2 ≤ 0}
  have hT : Continuous (fun p : ((CoordinateForm E × E) × S) => p.1.1) := continuous_fst.fst
  have hv : Continuous (fun p : ((CoordinateForm E × E) × S) => (p.2 : E)) := continuous_subtype_val.comp continuous_snd
  have hB : IsClosed B := by
    apply IsClosed.inter
    · exact isClosed_eq (continuous_fst.snd.inner (continuous_subtype_val.comp continuous_snd)) continuous_const
    · exact isClosed_le
        ((hT.clm_apply hv).clm_apply hv) continuous_const
  have hC : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace _ hB
  convert hC.isOpen_compl using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [mem_ofPred_eq, mem_compl_iff, mem_image, B]
  constructor
  · intro hp
    rintro ⟨y,hy,hyp⟩
    subst p
    exact (not_le_of_gt (hp y.2 (by simpa only [S, mem_sphere_zero_iff_norm] using y.2.property) hy.1)) hy.2
  · intro hp v hv hav
    by_contra hh
    apply hp
    exact ⟨(p,⟨v,by simpa [S,mem_sphere_zero_iff_norm] using hv⟩),⟨hav,not_lt.mp hh⟩,rfl⟩

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

local instance genericHessMapNorm_r0bfca6_1 : NormedAddCommGroup (E →L[ℝ] V) := inferInstance
attribute [local instance] OAI.YauCounterexamples.genericHessMapSpace
local instance genericHessFormNorm_r0bfca6_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance genericHessFormSpace_r0bfca6_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance
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

omit [FiniteDimensional ℝ E] in
lemma selfMetricFlat_metric_norm (g : SmoothMetric E E) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ v : TangentSpace 𝓘(ℝ,E) x,
      selfMetricFlat g x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v)
        ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v) = ‖v‖^2 := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  intro v
  have hn := real_inner_self_eq_norm_sq v
  change g.inner x v v = ‖v‖^2 at hn
  simpa only [selfMetricFlat,ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using hn


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

noncomputable section
section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
open Set Filter Function
open scoped Topology ContDiff
variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma preparationCorrugation_smooth {ψ χ : E → ℝ} {F₀ : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F₀) (hy : ContDiff ℝ ∞ y) (d N : ℝ) (τ : V) :
    ContDiff ℝ ∞ (preparationCorrugation ψ χ F₀ y d N τ) :=
  hψ.add (contDiff_const.mul (hχ.mul (hF.comp ((hy.const_smul N).add contDiff_const))))

end YauCounterexamples

end

open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples

lemma preparationWave_smooth : ContDiff ℝ ∞ preparationWave :=
  ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).neg).div_const _

lemma preparationWaveSecond_smooth : ContDiff ℝ ∞ preparationWaveSecond :=
  contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

lemma preparationWaveSecond_periodic : Function.Periodic preparationWaveSecond 1 := by
  intro t
  dsimp [preparationWaveSecond]
  rw [show 2*Real.pi*(t+1)=2*Real.pi*t+2*Real.pi by ring,Real.cos_add_two_pi]

end YauCounterexamples

end


namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_eq (g : SmoothMetric E E) (x v : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    actualCoordinateNorm g x v = ‖(NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm v‖ := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  have he := selfMetricFlat_metric_norm g x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm v)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at he
  rw [actualCoordinateNorm,he,Real.sqrt_sq (norm_nonneg _)]

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_nonneg (g : SmoothMetric E E) (x v : E) :
    0 ≤ actualCoordinateNorm g x v := Real.sqrt_nonneg _

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_pos (g : SmoothMetric E E) (x : E) {v : E} (hv : v ≠ 0) :
    0 < actualCoordinateNorm g x v := Real.sqrt_pos.mpr (selfMetricFlat_pos g x hv)

attribute [local instance] OAI.YauCounterexamples.globalPrepDualNorm
attribute [local instance] OAI.YauCounterexamples.globalPrepDualSpace
local instance globalPrepInvNorm_r0bfca6_1 : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance
local instance globalPrepInvSpace_r0bfca6_1 : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma continuous_actualCoordinateNorm (g : SmoothMetric E E) {v : E → E}
    (hv : Continuous v) : Continuous (fun x => actualCoordinateNorm g x (v x)) :=
  (((contDiff_selfMetricFlat g).continuous.clm_apply hv).clm_apply hv).sqrt

lemma continuous_actualProfileSpeed (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) : Continuous (actualProfileSpeed g u) :=
  continuous_actualCoordinateNorm g (contDiff_coordinateMetricGradient g hu).continuous

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_abs_sub (g : SmoothMetric E E) (x v w : E) :
    |actualCoordinateNorm g x v-actualCoordinateNorm g x w| ≤ actualCoordinateNorm g x (v-w) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  simp only [actualCoordinateNorm_eq,map_sub]
  exact abs_norm_sub_norm_le _ _

theorem compact_actual_gradient_error (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ D : ℝ, 0 < D ∧ ∀ u v : E → ℝ, ∀ x ∈ K,
      actualCoordinateNorm g x (coordinateMetricGradient g v x-coordinateMetricGradient g u x) ≤
        D*‖fderiv ℝ v x-fderiv ℝ u x‖ := by
  have hi : Continuous (fun x => (selfMetricFlat g x).inverse) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x
      (contDiff_selfMetricFlat g).contDiffAt).continuousAt
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (f:=selfMetricFlat g) (contDiff_selfMetricFlat g).continuous.continuousOn
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn (f:=fun x => (selfMetricFlat g x).inverse) hi.continuousOn
  let C := |B|+|A|+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg B,abs_nonneg A]
  have hCB : ∀ x ∈ K, ‖selfMetricFlat g x‖ ≤ C := by
    intro x hx
    exact (hB x hx).trans (by dsimp [C]; linarith [le_abs_self B,abs_nonneg A])
  have hCA : ∀ x ∈ K, ‖(selfMetricFlat g x).inverse‖ ≤ C := by
    intro x hx
    exact (hA x hx).trans (by dsimp [C]; linarith [le_abs_self A,abs_nonneg B])
  have hnorm : ∀ x ∈ K, ∀ w : E, actualCoordinateNorm g x w ≤ C*‖w‖ := by
    intro x hx w
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg hC.le (norm_nonneg _),?_⟩
    have hBww := (le_abs_self (selfMetricFlat g x w w)).trans
      ((selfMetricFlat g x).le_opNorm₂ w w)
    have hh := mul_le_mul_of_nonneg_right (hCB x hx) (sq_nonneg ‖w‖)
    have hc2 : C ≤ C ^ 2 := by nlinarith
    have hh2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖w‖)
    nlinarith
  refine ⟨C ^ 2,sq_pos_of_pos hC,?_⟩
  intro u v x hx
  have hg : coordinateMetricGradient g v x-coordinateMetricGradient g u x =
      (selfMetricFlat g x).inverse (fderiv ℝ v x-fderiv ℝ u x) := (map_sub _ _ _).symm
  rw [hg]
  calc
    _ ≤ C*‖(selfMetricFlat g x).inverse (fderiv ℝ v x-fderiv ℝ u x)‖ := hnorm x hx _
    _ ≤ C*(‖(selfMetricFlat g x).inverse‖*‖fderiv ℝ v x-fderiv ℝ u x‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hC.le
    _ ≤ C*(C*‖fderiv ℝ v x-fderiv ℝ u x‖) := by gcongr; exact hCA x hx
    _ = _ := by ring

lemma compact_actual_speed_pos (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {K : Set E} (hK : IsCompact K)
    (ha : ∀ x ∈ K, coordinateMetricGradient g u x ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ actualProfileSpeed g u x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hm⟩ := hK.exists_isMinOn hne (continuous_actualProfileSpeed g hu).continuousOn
    exact ⟨_,actualCoordinateNorm_pos g x (ha x hx),hm⟩
  · exact ⟨1,zero_lt_one,fun x hx => (hne ⟨x,hx⟩).elim⟩

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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma preparationCorrugation_tsupport (u χ s : E → ℝ) (C N τ : ℝ) :
    tsupport (fun x => preparationCorrugation u χ preparationWave s C N τ x-u x) ⊆
      tsupport χ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support,not_not] at hx
  simp [Function.mem_support,preparationCorrugation,hx]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma disjoint_sum_eventuallyEq {ι : Type*} [Fintype ι]
    (u : E → ℝ) (f : ι → E → ℝ)
    (hd : Pairwise (Disjoint on fun i => tsupport (f i))) (x : E) :
    ((fun y => u y+∑ i, f i y) =ᶠ[𝓝 x] u) ∨
      ∃ i, x ∈ tsupport (f i) ∧
        (fun y => u y+∑ j, f j y) =ᶠ[𝓝 x] (fun y => u y+f i y) := by
  classical
  by_cases hx : ∃ i, x ∈ tsupport (f i)
  · obtain ⟨i,hi⟩ := hx
    right
    refine ⟨i,hi,?_⟩
    have hz : ∀ j, ∀ᶠ y in 𝓝 x, j ≠ i → f j y = 0 := by
      intro j
      by_cases hji : j = i
      · exact Filter.Eventually.of_forall (fun _ hh => (hh hji).elim)
      · exact (notMem_tsupport_iff_eventuallyEq.mp ((hd hji).notMem_of_mem_right hi)).mono
          (fun _ hh _ => hh)
    filter_upwards [Filter.eventually_all.mpr hz] with y hy
    rw [Finset.sum_eq_single i (fun j _ hji => hy j hji) (by simp)]
  · left
    have hz : ∀ i, ∀ᶠ y in 𝓝 x, f i y = 0 := fun i =>
      notMem_tsupport_iff_eventuallyEq.mp (fun hh => hx ⟨i,hh⟩)
    filter_upwards [Filter.eventually_all.mpr hz] with y hy
    simp only [hy,Finset.sum_const_zero,add_zero]

theorem compact_relative_gradient_tolerance (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {K : Set E} (hK : IsCompact K)
    (ha : ∀ x ∈ K, coordinateMetricGradient g u x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : E → ℝ, ∀ x ∈ K,
      ‖fderiv ℝ v x-fderiv ℝ u x‖ < δ →
      actualCoordinateNorm g x (coordinateMetricGradient g v x-coordinateMetricGradient g u x) <
        ε*actualProfileSpeed g u x := by
  obtain ⟨D,hD,hbound⟩ := compact_actual_gradient_error g hK
  obtain ⟨m,hm,hmin⟩ := compact_actual_speed_pos g hu hK ha
  refine ⟨ε*m/D,by positivity,?_⟩
  intro v x hx hd
  calc
    _ ≤ D*‖fderiv ℝ v x-fderiv ℝ u x‖ := hbound u v x hx
    _ < D*(ε*m/D) := mul_lt_mul_of_pos_left hd hD
    _ = ε*m := by field_simp
    _ ≤ ε*actualProfileSpeed g u x := mul_le_mul_of_nonneg_left (hmin x hx) hε.le

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PreparationWaveSecondGtOne
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ENNReal NNReal Topology
namespace YauCounterexamples
variable {X G : Type*} [MeasurableSpace X] [MeasurableSpace G]
  [AddGroup G] [MeasurableAdd₂ G]
  (μ : Measure X) [SFinite μ] (ν : Measure G) [SFinite ν]
  [ν.IsAddLeftInvariant]

theorem periodic_phase_average (a : X → G) (ha : Measurable a)
    {E : Set G} (hE : MeasurableSet E) :
    (∫⁻ τ, μ {x | a x + τ ∈ E} ∂ν) = μ univ * ν E := by
  have hh : Measurable (fun p : X × G => E.indicator (fun _ => (1 : ℝ≥0∞)) (a p.1+p.2)) :=
    (measurable_const.indicator hE).comp ((ha.comp measurable_fst).add measurable_snd)
  have hleft (τ : G) : (∫⁻ x, E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ) ∂μ) =
      μ {x | a x+τ ∈ E} := by
    rw [show (fun x => E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ)) =
      ((fun x => a x+τ) ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)) by
        funext x; rfl]
    rw [lintegral_indicator (hE.preimage (ha.add_const τ)), lintegral_one, Measure.restrict_apply_univ]
    rfl
  have hright (x : X) : (∫⁻ τ, E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ) ∂ν) = ν E := by
    rw [show (fun τ => E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ)) =
      ((fun τ => a x+τ) ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)) by
        funext τ; rfl]
    have hm : Measurable (fun τ : G => a x + τ) := measurable_const.add measurable_id
    rw [lintegral_indicator (hE.preimage hm), lintegral_one, Measure.restrict_apply_univ]
    exact measure_preimage_add ν (a x) E
  calc
    _ = ∫⁻ τ, ∫⁻ x, E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ) ∂μ ∂ν := by simp_rw [hleft]
    _ = ∫⁻ x, ∫⁻ τ, E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ) ∂ν ∂μ :=
      (lintegral_lintegral_swap hh.aemeasurable).symm
    _ = _ := by simp [hright,mul_comm]

theorem exists_periodic_phase_mass [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (a : X → G) (ha : Measurable a) {E : Set G} (hE : MeasurableSet E) :
    ∃ τ : G, μ univ * ν E ≤ μ {x | a x+τ ∈ E} := by
  have hi := periodic_phase_average μ ν a ha hE
  obtain ⟨τ,hτ⟩ := exists_lintegral_le (μ:=ν)
    (f:=fun τ => μ {x | a x+τ ∈ E}) (by rw [hi]; exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
  exact ⟨τ,hi ▸ hτ⟩
end YauCounterexamples

end


namespace YauCounterexamples
noncomputable section
open Set Function MeasureTheory Metric
open scoped ENNReal

lemma preparationWaveSecond_gt_one_of_abs {t : ℝ} (ht : |t| < 1/6) :
    1 < preparationWaveSecond t := by
  have hπ := Real.pi_pos
  have harg : |2*Real.pi*t| < Real.pi/3 := by
    rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    nlinarith
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (2*Real.pi*t))
    (by linarith : Real.pi/3 ≤ Real.pi) harg
  rw [Real.cos_pi_div_three,Real.cos_abs] at hcos
  dsimp [preparationWaveSecond]
  linarith

lemma preparationWaveSecond_gt_one_of_circle {t : ℝ}
    (ht : (t : UnitAddCircle) ∈ ball 0 (1/6)) : 1 < preparationWaveSecond t := by
  have habs : |t-(round t : ℝ)| < 1/6 := by
    simpa only [mem_ball,dist_zero_right,AddCircle.norm_eq,inv_one,one_mul,mul_one] using ht
  have he := preparationWaveSecond_periodic.sub_int_mul_eq (x:=t) (round t)
  rw [mul_one] at he
  rw [←he]
  exact preparationWaveSecond_gt_one_of_abs habs

lemma preparation_phase_fraction :
    (volume : Measure UnitAddCircle) (ball 0 (1/6)) = (1/3 : ℝ≥0∞) := by
  rw [←measure_congr (AddCircle.closedBall_ae_eq_ball (x:=(0:UnitAddCircle)) (ε:=1/6)),
    AddCircle.volume_closedBall]
  norm_num [ENNReal.ofReal_div_of_pos]

theorem exists_preparation_phase {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (s : X → ℝ) (hs : Measurable s) (N : ℝ) :
    ∃ τ : ℝ, μ univ*(1/3 : ℝ≥0∞) ≤ μ {x | 1 < preparationWaveSecond (N*s x+τ)} := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  have ha : Measurable (fun x => ((N*s x : ℝ) : UnitAddCircle)) :=
    (AddCircle.continuous_mk' (1:ℝ)).measurable.comp (measurable_const.mul hs)
  obtain ⟨τ,hτ⟩ := exists_periodic_phase_mass μ (volume : Measure UnitAddCircle)
    (fun x => ((N*s x : ℝ) : UnitAddCircle)) ha (E:=ball 0 (1/6)) measurableSet_ball
  obtain ⟨τ,rfl⟩ := Quotient.exists_rep τ
  refine ⟨τ,?_⟩
  rw [preparation_phase_fraction] at hτ
  refine hτ.trans (measure_mono ?_)
  intro x hx
  apply preparationWaveSecond_gt_one_of_circle
  exact hx
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

lemma isOpen_metricJetFull (g : SmoothMetric E E) : IsOpen {z | metricJetFull g z} := by
  have h : IsOpen {p : CoordinateForm E × E | p.2 ≠ 0 ∧ quadraticPlaneFull p.1 p.2} :=
    (isOpen_ne_fun continuous_snd continuous_const).inter isOpen_quadraticPlaneFull
  exact h.preimage (continuous_metricJetMap g)

lemma metricJetFull_actual (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    metricJetFull g (x,actualCoordinateHessian g u x,fderiv ℝ u x) ↔
      coordinateMetricGradient g u x ≠ 0 ∧ actualProfileFull g u x := by
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactDisjointSmoothCutoffs
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Metric MeasureTheory
open scoped Topology ENNReal
open Set Filter Function Metric Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

theorem compact_disjoint_smooth_cutoffs (K V : ι → Set E)
    (hK : ∀ i, IsCompact (K i)) (hd : Pairwise (Disjoint on K))
    (hV : ∀ i, IsOpen (V i)) (hKV : ∀ i, K i ⊆ V i) :
    ∃ χ : ι → E → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧
        tsupport (χ i) ⊆ V i ∧ (∀ᶠ x in 𝓝ˢ (K i), χ i x = 1) ∧
        ∀ x, χ i x ∈ Icc 0 1) ∧ Pairwise (Disjoint on fun i => tsupport (χ i)) := by
  have hN : Pairwise (Disjoint on fun i => 𝓝ˢ (K i)) := by
    intro i j hij
    change Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j))
    rw [(hK i).disjoint_nhdsSet_left]
    intro x hx
    rw [(hK j).disjoint_nhdsSet_right]
    intro y hy
    exact disjoint_nhds_nhds.mpr (fun hxy => (hd hij).notMem_of_mem_left hx (hxy ▸ hy))
  obtain ⟨O,hO,hdO⟩ := hN.exists_mem_filter_basis_of_disjoint (fun i => hasBasis_nhdsSet (K i))
  have hex (i : ι) : ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ V i ∩ O i ∧ (∀ᶠ x in 𝓝ˢ (K i), χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
    obtain ⟨B,hB,hKB,hBc⟩ := exists_isOpen_superset_and_isCompact_closure (hK i)
    have hNV : V i ∩ O i ∩ B ∈ 𝓝ˢ (K i) :=
      ((hV i).inter (hO i).1 |>.inter hB).mem_nhdsSet.mpr
        (fun x hx => ⟨⟨hKV i hx,(hO i).2 hx⟩,hKB hx⟩)
    obtain ⟨W,hW,hKW,hWsub⟩ := (hK i).exists_isOpen_closure_subset hNV
    obtain ⟨f,hf1,hf0,hf⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓘(ℝ,E)) (n := ⊤) (hK i).isClosed (t := W) (by simpa only [hW.interior_eq] using hKW)
    have hfs : tsupport (f : E → ℝ) ⊆ closure W := by
      apply closure_mono
      intro x hx
      by_contra hh
      exact hx (hf0 x hh)
    refine ⟨f,contMDiff_iff_contDiff.mp f.contMDiff,?_,?_,hf1,hf⟩
    · exact hBc.of_isClosed_subset (isClosed_tsupport _)
        (hfs.trans (hWsub.trans (fun x hx => subset_closure hx.2)))
    · exact hfs.trans (hWsub.trans (fun x hx => hx.1))
  choose χ hχ using hex
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1.trans inter_subset_left,
    (hχ i).2.2.2.1,(hχ i).2.2.2.2⟩,?_⟩
  intro i j hij
  exact (hdO hij).mono ((hχ i).2.2.1.trans inter_subset_right)
    ((hχ j).2.2.1.trans inter_subset_right)
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_FinitePrepDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Metric MeasureTheory
open scoped Topology ENNReal
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem finite_disjoint_profile_cores (μ : Measure E) [SFinite μ]
    {U : Set E} (hU : IsOpen U) (V : E → Set E) (hV : ∀ x ∈ U, V x ∈ 𝓝 x)
    {a : ℝ≥0∞} (ha : a < μ U) :
    ∃ (t : Finset E) (r : E → ℝ),
      (∀ x ∈ t, x ∈ U ∧ 0 < r x ∧ closedBall x (r x) ⊆ U ∩ V x) ∧
      (t : Set E).PairwiseDisjoint (fun x => closedBall x (r x)) ∧
      a < μ (⋃ x ∈ t, closedBall x (r x)) := by
  classical
  let f : E → Set ℝ := fun x => {r | closedBall x r ⊆ U ∩ V x}
  have hf : ∀ x ∈ U, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty := by
    intro x hx δ hδ
    have hn : U ∩ V x ∈ 𝓝 x := inter_mem (hU.mem_nhds hx) (hV x hx)
    obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hn
    refine ⟨min r δ / 2, ⟨?_, by constructor <;> nlinarith [lt_min hr hδ, min_le_right r δ]⟩⟩
    exact (closedBall_subset_ball (by nlinarith [lt_min hr hδ, min_le_left r δ])).trans hrsub
  obtain ⟨s,r,hs,hsU,hr,hcover,hdisj⟩ :=
    Besicovitch.exists_disjoint_closedBall_covering_ae μ f U hf (fun _ => 1) (by intro x hx; norm_num)
  have hμ : μ (⋃ x ∈ s, closedBall x (r x)) = μ U := by
    apply le_antisymm (measure_mono ?_)
    · exact measure_mono_ae (ae_le_set.mpr hcover)
    · intro y hy
      obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
      exact (hr x hx).1 hy |>.1
  let : Countable s := hs.to_subtype
  let A : Finset s → Set E := fun t => ⋃ x ∈ t, closedBall (x : E) (r x)
  have hmono : Monotone A := by
    intro t v htv y hy
    obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨x,htv hx,hy⟩
  have hUnion : (⋃ t : Finset s, A t) = ⋃ x ∈ s, closedBall x (r x) := by
    ext y
    simp only [A, mem_iUnion]
    constructor
    · rintro ⟨t,x,hx,hy⟩
      exact ⟨x,x.property,hy⟩
    · rintro ⟨x,hx,hy⟩
      exact ⟨{⟨x,hx⟩},⟨x,hx⟩,Finset.mem_singleton_self _,hy⟩
  have hsup : a < ⨆ t : Finset s, μ (A t) := by
    rw [← hmono.measure_iUnion, hUnion, hμ]
    exact ha
  obtain ⟨t,ht⟩ := lt_iSup_iff.mp hsup
  refine ⟨t.image Subtype.val,r,?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hsU y.property,(hr y y.property).2.1,(hr y y.property).1⟩
  · intro x hx y hy hxy
    obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
    exact hdisj x'.property y'.property hxy
  · simpa [A] using ht
end YauCounterexamples

end

namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma disjoint_supported_sum_eq_patch {ι : Type*} [Fintype ι]
    (u : E → ℝ) (χ f : ι → E → ℝ)
    (hd : Pairwise (Disjoint on fun i => tsupport (χ i)))
    (hf : ∀ i, tsupport (f i) ⊆ tsupport (χ i)) {i : ι} {x : E}
    (hx : x ∈ tsupport (χ i)) :
    (fun y => u y+∑ j, f j y) =ᶠ[𝓝 x] (fun y => u y+f i y) := by
  classical
  have hz : ∀ j, ∀ᶠ y in 𝓝 x, j ≠ i → f j y = 0 := by
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ hh => (hh hji).elim)
    · exact (notMem_tsupport_iff_eventuallyEq.mp
        (fun hh => (hd hji).notMem_of_mem_right hx (hf j hh))).mono (fun _ hh _ => hh)
  filter_upwards [Filter.eventually_all.mpr hz] with y hy
  rw [Finset.sum_eq_single i (fun j _ hji => hy j hji) (by simp)]

local instance finitePrepDualNorm_r0bfca6_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
theorem actual_metric_preparation (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g u x ≠ 0)
    (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g u x)
    (μ : Measure E) [IsFiniteMeasure μ] {ε εp : ℝ} (hε : 0 < ε) (hεp : 0 < εp) :
    ∃ (v : E → ℝ) (U : Set E), ContDiff ℝ ∞ v ∧
      HasCompactSupport (fun x => v x-u x) ∧ tsupport (fun x => v x-u x) ⊆ Ω ∧
      (∀ x, |v x-u x| < ε ∧ ‖fderiv ℝ v x-fderiv ℝ u x‖ < ε) ∧
      (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
        actualCoordinateNorm g x (coordinateMetricGradient g v x-coordinateMetricGradient g u x) ≤
          εp*actualProfileSpeed g u x) ∧
      IsOpen U ∧ U ⊆ Ω ∧ (∀ x ∈ U, actualProfileFull g v x) ∧ μ Ω/6 ≤ μ U := by
  classical
  by_cases hzero : μ Ω = 0
  · refine ⟨u,∅,hu,?_,?_,?_,?_,isOpen_empty,empty_subset _,?_,?_⟩
    · dsimp [HasCompactSupport]; simp
    · simp
    · intro x; simpa using And.intro hε hε
    · intro x hx
      refine ⟨ha x hx,hstrict x hx,?_⟩
      simp only [sub_self,actualCoordinateNorm,map_zero,Real.sqrt_zero]
      exact mul_nonneg hεp.le (actualCoordinateNorm_nonneg g _ _)
    · simp
    · simp [hzero]
  have hhalf : μ Ω/2 < μ Ω := by
    have hh := ENNReal.mul_lt_mul_left hzero (measure_ne_top μ Ω)
      (by norm_num : (1/2 : ℝ≥0∞) < 1)
    simpa only [one_mul,div_eq_mul_inv,one_mul,mul_comm] using hh
  have hloc : ∀ p : E, ∃ (W : Set E) (s : E → ℝ) (C : ℝ), IsOpen W ∧
      (p ∈ Ω → p ∈ W ∧ ContDiff ℝ ∞ s ∧ 0 < C ∧ ∀ x ∈ W,
        fderiv ℝ s x ≠ 0 ∧ fderiv ℝ s x (coordinateMetricGradient g u x) = 0 ∧
        ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0) ∧
        (∀ c ∈ Icc (-2*C) (2*C), quadraticPlaneStrict
          (metricProfileTraceForm (selfMetricFlat g x)
            (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
            (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ∧
        (∀ c ∈ Icc C (2*C), quadraticPlaneFull
          (metricProfileTraceForm (selfMetricFlat g x)
            (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
            (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)))) := by
    intro p
    by_cases hp : p ∈ Ω
    · obtain ⟨W,s,C,hWo,hWp,hs,hC,hdata⟩ := exists_actual_preparation_neighborhood hdim g hu
        (ha p (subset_closure hp)) (hstrict p (subset_closure hp))
      exact ⟨W,s,C,hWo,fun _ => ⟨hWp,hs,hC,hdata⟩⟩
    · exact ⟨∅,0,1,isOpen_empty,fun h => (hp h).elim⟩
  choose W s C hWo hW using hloc
  obtain ⟨t,r,ht,htd,htm⟩ := finite_disjoint_profile_cores μ hΩ W
    (fun p hp => (hWo p).mem_nhds (hW p hp).1) hhalf
  let ι := {p // p ∈ t}
  let K : ι → Set E := fun i => closedBall i.val (r i.val)
  have hK : ∀ i, IsCompact (K i) := fun _ => isCompact_closedBall _ _
  have hKd : Pairwise (Disjoint on K) := by
    intro i j hij
    exact htd i.property j.property (fun he => hij (Subtype.ext he))
  obtain ⟨χ,hχ,hχd⟩ := compact_disjoint_smooth_cutoffs K (fun i => Ω ∩ W i.val) hK hKd
    (fun i => hΩ.inter (hWo i.val)) (fun i => (ht i.val i.property).2.2)
  have hχ1 : ∀ i, ∀ x ∈ K i, χ i x = 1 := fun i x hx =>
    (eventually_nhdsSet_iff_forall.mp (hχ i).2.2.2.1 x hx).self_of_nhds
  have hKχ : ∀ i, K i ⊆ tsupport (χ i) := by
    intro i x hx
    apply subset_tsupport
    simp only [Function.mem_support,hχ1 i x hx,ne_eq,one_ne_zero,not_false_eq_true]
  obtain ⟨δ,hδ,hrel⟩ := compact_relative_gradient_tolerance g hu hΩc ha hεp
  have hpdata : ∀ i : ι, ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ τ : ℝ,
      ∀ x ∈ tsupport (χ i),
      let v := preparationCorrugation u (χ i) preparationWave (s i.val) (C i.val) N τ
      coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
      (χ i x = 1 → 1 < preparationWaveSecond (N*s i.val x+τ) → actualProfileFull g v x) ∧
      |v x-u x| < min ε δ ∧ ‖fderiv ℝ v x-fderiv ℝ u x‖ < min ε δ := by
    intro i
    have hi := hW i.val (ht i.val i.property).1
    apply actual_preparation_on_compact_patch g hu (hχ i).1 hi.2.1 (hχ i).2.1
      (C i.val) hi.2.2.1 (fun x _ => (hχ i).2.2.2.2 x)
    · exact fun x hx => (hi.2.2.2 x ((hχ i).2.2.1 hx).2).2.2.1
    · exact fun x hx => (hi.2.2.2 x ((hχ i).2.2.1 hx).2).2.2.2.1
    · exact fun x hx => (hi.2.2.2 x ((hχ i).2.2.1 hx).2).2.2.2.2
    · exact lt_min hε hδ
  choose N₀ hN₀ hdata using hpdata
  let N : ℝ := max 1 (∑ i, |N₀ i|)
  have hN : ∀ i, N₀ i ≤ N := by
    intro i
    exact (le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (N₀ j))
      (Finset.mem_univ i)).trans (le_max_right _ _))
  let S : Set E := ⋃ i, K i
  have hSm : MeasurableSet S := MeasurableSet.iUnion fun i => (hK i).measurableSet
  have hSO : S ⊆ Ω := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact ((ht i.val i.property).2.2 hi).1
  have hMS : μ Ω/2 ≤ μ S := by
    apply le_of_lt
    convert htm using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    simp only [S,K,ι,mem_iUnion,Subtype.exists,exists_prop]
  let sg : E → ℝ := fun x => ∑ i, (K i).indicator (s i.val) x
  have hsg : Measurable sg := Finset.measurable_sum _ (fun i _ =>
    ((hW i.val (ht i.val i.property).1).2.1.continuous.measurable).indicator (hK i).measurableSet)
  have hsgi : ∀ i, ∀ x ∈ K i, sg x = s i.val x := by
    intro i x hx
    dsimp only [sg]
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem hx _
    · intro j _ hji
      exact indicator_of_notMem ((hKd hji).notMem_of_mem_right hx) _
    · simp
  obtain ⟨τ,hτ⟩ := exists_preparation_phase (μ.restrict S) sg hsg N
  let w : ι → E → ℝ := fun i => preparationCorrugation u (χ i) preparationWave (s i.val) (C i.val) N τ
  let f : ι → E → ℝ := fun i x => w i x-u x
  let v : E → ℝ := fun x => u x+∑ i, f i x
  have hw : ∀ i, ContDiff ℝ ∞ (w i) := fun i => preparationCorrugation_smooth hu (hχ i).1
    preparationWave_smooth (hW i.val (ht i.val i.property).1).2.1 _ _ _
  have hv : ContDiff ℝ ∞ v := hu.add (ContDiff.sum (fun i _ => (hw i).sub hu))
  have hfs : ∀ i, tsupport (f i) ⊆ tsupport (χ i) := fun i => preparationCorrugation_tsupport ..
  have hfd : Pairwise (Disjoint on fun i => tsupport (f i)) := fun i j hij =>
    (hχd hij).mono (hfs i) (hfs j)
  have heq : ∀ i, ∀ x ∈ tsupport (χ i), v =ᶠ[𝓝 x] w i := by
    intro i x hx
    simpa only [f,add_sub_cancel] using disjoint_supported_sum_eq_patch u χ f hχd hfs hx
  have hcases (x : E) : (v =ᶠ[𝓝 x] u) ∨ ∃ i, x ∈ tsupport (χ i) ∧ v =ᶠ[𝓝 x] w i := by
    rcases disjoint_sum_eventuallyEq u f hfd x with h|⟨i,hi,hei⟩
    · exact Or.inl h
    · exact Or.inr ⟨i,hfs i hi,heq i x (hfs i hi)⟩
  have hvs : tsupport (fun x => v x-u x) ⊆ ⋃ i, tsupport (χ i) := by
    apply closure_minimal _ (isClosed_iUnion_of_finite fun i => isClosed_tsupport _)
    intro x hx
    by_contra hh
    have hz : ∀ i, χ i x = 0 := fun i => image_eq_zero_of_notMem_tsupport
      (fun hi => hh (mem_iUnion_of_mem i hi))
    have hvx : v x = u x := by simp [v,f,w,preparationCorrugation,hz]
    exact hx (sub_eq_zero.mpr hvx)
  have hc : HasCompactSupport (fun x => v x-u x) :=
    (isCompact_iUnion fun i => (hχ i).2.1).of_isClosed_subset (isClosed_tsupport _) hvs
  have hsub : tsupport (fun x => v x-u x) ⊆ Ω := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hvs hx)
    exact ((hχ i).2.2.1 hi).1
  have heps : ∀ x, |v x-u x| < ε ∧ ‖fderiv ℝ v x-fderiv ℝ u x‖ < ε := by
    intro x
    rcases hcases x with hh|⟨i,hi,hei⟩
    · simp only [hh.self_of_nhds,hh.fderiv_eq (𝕜:=ℝ),sub_self,abs_zero,norm_zero]
      exact ⟨hε,hε⟩
    · have hp := hdata i N (hN i) τ x hi
      rw [hei.self_of_nhds,hei.fderiv_eq (𝕜:=ℝ)]
      exact ⟨hp.2.2.2.1.trans_le (min_le_left _ _),hp.2.2.2.2.trans_le (min_le_left _ _)⟩
  have hglobal : ∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
      actualCoordinateNorm g x (coordinateMetricGradient g v x-coordinateMetricGradient g u x) ≤
        εp*actualProfileSpeed g u x := by
    intro x hx
    rcases hcases x with hh|⟨i,hi,hei⟩
    · obtain ⟨hg,hH,hS,hF⟩ := actualJet_eventuallyEq g hh
      refine ⟨hg ▸ ha x hx,hS.mpr (hstrict x hx),?_⟩
      simp only [hg,sub_self,actualCoordinateNorm,map_zero,Real.sqrt_zero]
      exact mul_nonneg hεp.le (actualCoordinateNorm_nonneg g _ _)
    · have hp := hdata i N (hN i) τ x hi
      obtain ⟨hg,hH,hS,hF⟩ := actualJet_eventuallyEq g hei
      refine ⟨hg ▸ hp.1,hS.mpr hp.2.1,?_⟩
      exact (hrel v x hx (by
        rw [hei.fderiv_eq (𝕜:=ℝ)]
        exact hp.2.2.2.2.trans_le (min_le_right _ _))).le
  let U : Set E := Ω ∩ {x | metricJetFull g (x,actualCoordinateHessian g v x,fderiv ℝ v x)}
  have hU : IsOpen U := hΩ.inter ((isOpen_metricJetFull g).preimage
    (continuous_id.prodMk ((continuous_coordinateCovariantSecond _
      (contDiff_metricChristoffel g).continuous hv).prodMk (hv.continuous_fderiv (by simp)))))
  have hUF : ∀ x ∈ U, actualProfileFull g v x := fun x hx =>
    ((metricJetFull_actual g v x).mp hx.2).2
  have hgood : {x | 1 < preparationWaveSecond (N*sg x+τ)} ∩ S ⊆ U := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx.2
    have hix := hKχ i hi
    have hp := hdata i N (hN i) τ x hix
    have hh := hp.2.2.1 (hχ1 i x hi) (by simpa only [mem_ofPred_eq,hsgi i x hi] using hx.1)
    have he := actualJet_eventuallyEq g (heq i x hix)
    exact ⟨hSO hx.2,(metricJetFull_actual g v x).mpr ⟨(hglobal x (subset_closure (hSO hx.2))).1,
      he.2.2.2.mpr hh⟩⟩
  refine ⟨v,U,hv,hc,hsub,heps,hglobal,hU,inter_subset_left,hUF,?_⟩
  have hmeas : MeasurableSet {x | 1 < preparationWaveSecond (N*sg x+τ)} :=
    measurableSet_lt measurable_const (preparationWaveSecond_smooth.continuous.measurable.comp
      ((measurable_const.mul hsg).add measurable_const))
  rw [Measure.restrict_apply_univ,Measure.restrict_apply hmeas] at hτ
  calc
    μ Ω/6 = μ Ω/2*(1/3 : ℝ≥0∞) := by
      simp only [div_eq_mul_inv,mul_assoc,one_mul]
      congr 1
      rw [← ENNReal.mul_inv (by norm_num : (2 : ℝ≥0∞) ≠ 0 ∨ (3 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))
        (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) ∨ (3 : ℝ≥0∞) ≠ 0)]
      norm_num
    _ ≤ μ S*(1/3 : ℝ≥0∞) := by gcongr
    _ ≤ μ ({x | 1 < preparationWaveSecond (N*sg x+τ)} ∩ S) := hτ
    _ ≤ μ U := measure_mono hgood
end
end YauCounterexamples

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

lemma FixedRadialChoice.fraction_le (D : FixedRadialChoice) : D.fraction ≤ 1 := by
  dsimp [FixedRadialChoice.fraction]
  nlinarith [D.radius_pos,D.radius_le]

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

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma actualProfileMass_nonneg (g : SmoothMetric E E) (u : E → ℝ) (μ : Measure E) (Ω : Set E) :
    0 ≤ actualProfileMass g u μ Ω := integral_nonneg (actualProfileSpeed_nonneg g u)

lemma actualProfileWeightedMeasure_finite (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {Ω : Set E} (hΩ : IsCompact (closure Ω))
    (μ : Measure E) [IsLocallyFiniteMeasure μ] :
    IsFiniteMeasure (actualProfileWeightedMeasure g u μ Ω) :=
  isFiniteMeasure_withDensity_ofReal (integrableOn_actualProfileSpeed g hu hΩ μ).2

lemma actualProfileWeightedMeasure_apply (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {Ω : Set E} (hΩ : IsCompact (closure Ω))
    (μ : Measure E) [IsLocallyFiniteMeasure μ] {S : Set E} (hS : MeasurableSet S) :
    actualProfileWeightedMeasure g u μ Ω S =
      ENNReal.ofReal (∫ x in S, actualProfileSpeed g u x ∂(μ.restrict Ω)) := by
  rw [actualProfileWeightedMeasure,withDensity_apply _ hS]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrableOn_actualProfileSpeed g hu hΩ μ).integrableOn
    (ae_of_all _ (actualProfileSpeed_nonneg g u))).symm

lemma actualProfileWeightedMeasure_self (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {Ω : Set E} (hΩ : IsCompact (closure Ω)) (hΩm : MeasurableSet Ω)
    (μ : Measure E) [IsLocallyFiniteMeasure μ] :
    actualProfileWeightedMeasure g u μ Ω Ω = ENNReal.ofReal (actualProfileMass g u μ Ω) := by
  rw [actualProfileWeightedMeasure_apply g hu hΩ μ hΩm,Measure.restrict_restrict hΩm,
    inter_self,actualProfileMass]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma actualProfileSpeed_relative_error (g : SmoothMetric E E) (u v : E → ℝ) (x : E)
    {ε : ℝ} (h : actualCoordinateNorm g x
      (coordinateMetricGradient g v x-coordinateMetricGradient g u x) ≤ ε*actualProfileSpeed g u x) :
    (1-ε)*actualProfileSpeed g u x ≤ actualProfileSpeed g v x ∧
      actualProfileSpeed g v x ≤ (1+ε)*actualProfileSpeed g u x := by
  have hh := (actualCoordinateNorm_abs_sub g x
    (coordinateMetricGradient g v x) (coordinateMetricGradient g u x)).trans h
  change |actualProfileSpeed g v x-actualProfileSpeed g u x| ≤ ε*actualProfileSpeed g u x at hh
  obtain ⟨hl,hr⟩ := abs_le.mp hh
  constructor <;> linarith

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ActualProfileCycleGain
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem profile_mass_gain {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (E : Set X) (hE : MeasurableSet E) (ε γ θ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hbase : ∀ᵐ x ∂μ, (1-ε)*f x ≤ g x)
    (hcore : ∀ᵐ x ∂μ, x ∈ E → (1+γ)*f x ≤ g x)
    (hmass : θ*(∫ x, f x ∂μ) ≤ ∫ x in E, f x ∂μ) :
    (1-ε+γ*θ)*(∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ := by
  have hi := hf.indicator hE
  have hpoint : ∀ᵐ x ∂μ, (1-ε)*f x+γ*(E.indicator f x) ≤ g x := by
    filter_upwards [hf0,hbase,hcore] with x hx hb hc
    by_cases he : x ∈ E
    · rw [Set.indicator_of_mem he]
      have hh := hc he
      nlinarith [mul_nonneg hε hx]
    · rw [Set.indicator_of_notMem he,mul_zero,add_zero]
      exact hb
  have hle := integral_mono_ae ((hf.const_mul (1-ε)).add (hi.const_mul γ)) hg hpoint
  simp only [Pi.add_apply] at hle
  rw [integral_add (hf.const_mul (1-ε)) (hi.const_mul γ),integral_const_mul,
    integral_const_mul,integral_indicator hE] at hle
  have hh := mul_le_mul_of_nonneg_left hmass hγ
  nlinarith

theorem profile_cycle_numerics (M P Q t : ℝ) (hM : 0 ≤ M)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hP : (1-t/16)*M ≤ P) (hQ : (1+3*t/8)*P ≤ Q) :
    (1+t/4)*M ≤ Q := by
  have hp := mul_le_mul_of_nonneg_left hP (show 0 ≤ 1+3*t/8 by positivity)
  have hquad : t^2 ≤ t := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hquad hM
  nlinarith only [hp,hQ,hh,mul_nonneg ht.le hM]


end

open Set MeasureTheory Filter
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem actual_metric_profile_cycle_oai (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g u x ≠ 0)
    (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g u x)
    (μ : Measure E) [IsLocallyFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport (fun x => v x-u x) ∧
      tsupport (fun x => v x-u x) ⊆ Ω ∧ (∀ x, |v x-u x| < ε) ∧
      (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x) ∧
      (1+actualProfileCycleGain)*actualProfileMass g u μ Ω ≤ actualProfileMass g v μ Ω := by
  let D := fixedRadialChoice
  let θ := D.fraction/192
  let t := θ*D.g₀
  have hθ : 0 < θ := div_pos D.fraction_pos (by norm_num)
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith [D.fraction_le]
  have ht : 0 < t := mul_pos hθ D.gain_pos
  have ht1 : t ≤ 1 := (mul_le_mul hθ1 D.gain_le D.gain_pos.le (by norm_num)).trans_eq (by ring)
  have htg : t ≤ D.g₀ := by dsimp [t]; nlinarith [D.gain_pos]
  let ν := μ.restrict Ω
  let M := actualProfileMass g u μ Ω
  have hM : 0 ≤ M := actualProfileMass_nonneg g u μ Ω
  have huI : Integrable (actualProfileSpeed g u) ν := integrableOn_actualProfileSpeed g hu hΩc μ
  have hΩae : ∀ᵐ x ∂ν, x ∈ Ω := ae_restrict_mem hΩ.measurableSet
  let := actualProfileWeightedMeasure_finite g hu hΩc μ
  obtain ⟨ψ,U,hψ,hψc,hψs,hψ0,hψp,hU,hUΩ,hfull,hUm⟩ := actual_metric_preparation
    hdim g hu hΩ hΩc ha hstrict (actualProfileWeightedMeasure g u μ Ω)
    (half_pos hε) (show 0 < t/16 by positivity)
  have hψI : Integrable (actualProfileSpeed g ψ) ν := integrableOn_actualProfileSpeed g hψ hΩc μ
  let P := actualProfileMass g ψ μ Ω
  have hP : 0 ≤ P := actualProfileMass_nonneg g ψ μ Ω
  have hrel : ∀ᵐ x ∂ν, (1-t/16)*actualProfileSpeed g u x ≤ actualProfileSpeed g ψ x ∧
      actualProfileSpeed g ψ x ≤ (1+t/16)*actualProfileSpeed g u x := by
    filter_upwards [hΩae] with x hx
    exact actualProfileSpeed_relative_error g u ψ x (hψp x (subset_closure hx)).2.2
  have hPlow : (1-t/16)*M ≤ P := by
    have hh := integral_mono_ae (huI.const_mul (1-t/16)) hψI (hrel.mono fun _ h => h.1)
    simpa only [integral_const_mul,M,P,actualProfileMass,ν] using hh
  have hPup : P ≤ (1+t/16)*M := by
    have hh := integral_mono_ae hψI (huI.const_mul (1+t/16)) (hrel.mono fun _ h => h.2)
    simpa only [integral_const_mul,M,P,actualProfileMass,ν] using hh
  let Mu := ∫ x in U, actualProfileSpeed g u x ∂ν
  let Pu := ∫ x in U, actualProfileSpeed g ψ x ∂ν
  have hMu : 0 ≤ Mu := integral_nonneg (actualProfileSpeed_nonneg g u)
  have hPu : 0 ≤ Pu := integral_nonneg (actualProfileSpeed_nonneg g ψ)
  have hMupos : M/6 ≤ Mu := by
    rw [actualProfileWeightedMeasure_self g hu hΩc hΩ.measurableSet μ,
      actualProfileWeightedMeasure_apply g hu hΩc μ hU.measurableSet] at hUm
    change ENNReal.ofReal M/6 ≤ ENNReal.ofReal Mu at hUm
    have hh := ENNReal.toReal_mono (by simp) hUm
    simpa only [ENNReal.toReal_div,ENNReal.toReal_ofReal hM,ENNReal.toReal_ofReal hMu,
      ENNReal.toReal_ofNat] using hh
  have hMulow : (1-t/16)*Mu ≤ Pu := by
    have hh := integral_mono_ae (μ:=ν.restrict U) (huI.integrableOn.const_mul (1-t/16)) hψI.integrableOn
      (ae_restrict_of_ae (hrel.mono fun _ h => h.1))
    simpa only [integral_const_mul] using hh
  have hMuLow' : (2/3:ℝ)*Mu ≤ Pu := by nlinarith [mul_nonneg (show 0 ≤ 1/3-t/16 by linarith) hMu]
  have hPup' : P ≤ (4/3:ℝ)*M := by nlinarith [mul_nonneg (show 0 ≤ 1/3-t/16 by linarith) hM]
  have hPufrac : P/12 ≤ Pu := by linarith
  let := actualProfileWeightedMeasure_finite g hψ hΩc μ
  obtain ⟨v,G,hv,hvc,hvs,hv0,hvp,hG,hGU,hGm,hgain⟩ := actual_metric_radial_finite
    hdim g hψ hU hUΩ (fun x hx => (hψp x hx).1) (fun x hx => (hψp x hx).2.1) hfull
    (actualProfileWeightedMeasure g ψ μ Ω) D.smooth D.zero_at_zero D.range_bound
    (r:=1/8) (b:=1/256) (show (0:ℝ) ≤ 1/8 by norm_num) (by norm_num) (by norm_num)
    (by norm_num) D.zero_above D.delta_pos D.speed_pos.le
    (show 0 < t/8 by positivity) (show t/8 < 1 by linarith) (half_pos hε)
    D.Fmax D.S D.K D.Fmax_pos D.S_pos D.K_pos D.coefficients D.smallness
    D.q D.radius_pos D.radius_le D.window
  have hvI : Integrable (actualProfileSpeed g v) ν := integrableOn_actualProfileSpeed g hv hΩc μ
  have hGmass : θ*P ≤ ∫ x in G, actualProfileSpeed g ψ x ∂ν := by
    rw [actualProfileWeightedMeasure_apply g hψ hΩc μ hU.measurableSet,
      actualProfileWeightedMeasure_apply g hψ hΩc μ hG] at hGm
    have hGP : 0 ≤ ∫ x in G, actualProfileSpeed g ψ x ∂ν := integral_nonneg (actualProfileSpeed_nonneg g ψ)
    change ENNReal.ofReal Pu/2 * ENNReal.ofReal D.fraction ≤ ENNReal.ofReal (∫ x in G, actualProfileSpeed g ψ x ∂ν) at hGm
    have hh := ENNReal.toReal_mono (by simp) hGm
    simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_ofReal hPu,
      ENNReal.toReal_ofNat,ENNReal.toReal_ofReal D.fraction_pos.le,ENNReal.toReal_ofReal hGP] at hh
    change Pu/2*D.fraction ≤ _ at hh
    have hm := mul_le_mul_of_nonneg_right hPufrac D.fraction_pos.le
    dsimp [θ]
    nlinarith [mul_nonneg D.fraction_pos.le hP]
  have hbase : ∀ᵐ x ∂ν, (1-t/8)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x := by
    filter_upwards [hΩae] with x hx
    exact (hvp x (subset_closure hx)).2.2
  have hcore : ∀ᵐ x ∂ν, x ∈ G → (1+D.g₀/2)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x := by
    apply ae_of_all
    intro x hx
    have hh := hgain x hx
    have he := D.gain_eq
    have hp := actualProfileSpeed_nonneg g ψ x
    nlinarith [mul_nonneg (show 0 ≤ D.g₀/2-t/8 by linarith) hp]
  have hQ : (1+3*t/8)*P ≤ actualProfileMass g v μ Ω := by
    have hh := profile_mass_gain ν (actualProfileSpeed g ψ) (actualProfileSpeed g v)
      hψI hvI G hG (t/8) (D.g₀/2) θ (by positivity) (by linarith [D.gain_pos])
      (ae_of_all _ (actualProfileSpeed_nonneg g ψ)) hbase hcore hGmass
    have he : 1-t/8+(D.g₀/2)*θ = 1+3*t/8 := by dsimp [t]; ring
    rw [he] at hh
    exact hh
  refine ⟨v,hv,?_,?_,?_,(fun x hx => ⟨(hvp x hx).1,(hvp x hx).2.1⟩),?_⟩
  · have he : ((fun x => v x-ψ x)+(fun x => ψ x-u x)) = (fun x => v x-u x) := by
      funext x; dsimp; ring
    exact he ▸ hvc.add hψc
  · have hs := (tsupport_add (fun x => v x-ψ x) (fun x => ψ x-u x)).trans
      (union_subset (hvs.trans hUΩ) hψs)
    simpa only [Pi.add_apply,sub_add_sub_cancel] using hs
  · intro x
    calc |v x-u x| = |(v x-ψ x)+(ψ x-u x)| := by congr 1; ring
      _ ≤ |v x-ψ x|+|ψ x-u x| := abs_add_le _ _
      _ < ε/2+ε/2 := add_lt_add (hv0 x) (hψ0 x).1
      _ = ε := by ring
  · have hh := profile_cycle_numerics M P (actualProfileMass g v μ Ω) t hM ht ht1 hPlow hQ
    have he : actualProfileCycleGain = t/4 := by dsimp [actualProfileCycleGain,t,θ,D]; ring
    rwa [he]



end YauCounterexamples
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.YauCounterexamples.actual_metric_profile_cycle_oai.{u_1} := @OAI.YauCounterexamples.actual_metric_profile_cycle_oai.{u_1}
