-- Prove2me | solution 1 for OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:55:01.491216+00:00
-- url     : https://prove2.me/submissions/8f8c0432-3ec8-4429-a9cb-653188cc8ad4

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_C1ExtensionNearCompact
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
namespace YauCounterexamples
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma C1_extension_near_compact {K O : Set E} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) {φ : E → F} (hφ : ContDiffOn ℝ 1 φ O) :
    ∃ ψ : E → F, ContDiff ℝ 1 ψ ∧ φ =ᶠ[𝓝ˢ K] ψ := by
  obtain ⟨V, hV, hKV, hVO⟩ := normal_exists_closure_subset hK.isClosed hO hKO
  obtain ⟨η, hηone, hηzero, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, E)) (n := 1) (t := V)
      hK.isClosed (by simpa only [hV.interior_eq] using hKV)
  have hη : ContDiff ℝ 1 η := contMDiff_iff_contDiff.mp η.contMDiff
  have hsη : tsupport η ⊆ O := by
    apply (closure_mono (show support η ⊆ V from ?_)).trans hVO
    intro x hx
    by_contra hn
    exact hx (hηzero x hn)
  refine ⟨fun x => η x • φ x, ?_, ?_⟩
  · rw [← contMDiff_iff_contDiff]
    apply contMDiff_of_tsupport
    intro x hx
    have hxO : x ∈ O := hsη (tsupport_smul_subset_left η φ hx)
    rw [contMDiffAt_iff_contDiffAt]
    exact hη.contDiffAt.smul ((hφ x hxO).contDiffAt (hO.mem_nhds hxO))
  · filter_upwards [hηone] with x hx
    simp only [hx, one_smul]
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_LocalIntegrationPartsC1
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
namespace YauCounterexamples
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma local_integration_by_parts_C1 {O : Set E} (hO : IsOpen O)
    {f F : E → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ O) (hF : ContDiffOn ℝ 1 F O) (v : E) :
    (∫ x in O, f x * fderiv ℝ F x v) = -(∫ x in O, fderiv ℝ f x v * F x) := by
  obtain ⟨H, hH, he⟩ := C1_extension_near_compact hfc hO hfs hF
  have he' (x : E) (hx : x ∈ tsupport f) : F =ᶠ[𝓝 x] H :=
    he.filter_mono (nhds_le_nhdsSet hx)
  have hdf := (hf.fderiv_right (m := 0) (by simp)).clm_apply (contDiff_const (c := v))
  have hdH := (hH.fderiv_right (m := 0) (by simp)).clm_apply (contDiff_const (c := v))
  have h1 (x : E) : f x * fderiv ℝ F x v = f x * fderiv ℝ H x v := by
    by_cases hx : x ∈ tsupport f
    · rw [(he' x hx).fderiv_eq]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have h2 (x : E) : fderiv ℝ f x v * F x = fderiv ℝ f x v * H x := by
    by_cases hx : x ∈ tsupport f
    · rw [(he' x hx).eq_of_nhds]
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  simp_rw [h1, h2]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (mt (@hfs x) hx), zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [fderiv_of_notMem_tsupport ℝ (mt (@hfs x) hx)]; simp)]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (hdf.continuous.mul hH.continuous |>.integrable_of_hasCompactSupport
      ((hfc.fderiv_apply ℝ v).mul_right))
    (hf.continuous.mul hdH.continuous |>.integrable_of_hasCompactSupport hfc.mul_right)
    (hf.continuous.mul hH.continuous |>.integrable_of_hasCompactSupport hfc.mul_right)
    (fun x _ => (hf.differentiable (by simp)).differentiableAt)
    (fun x _ => (hH.differentiable (by simp)).differentiableAt)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LocalIntegrationParts
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma realChartLocalize_eq (p : M) (u : M → ℝ) {y : E} (hy : y ∈ (chartAt E p).target) :
    realChartLocalize (E := E) p u y = u ((chartAt E p).symm y) := ite_eq_left hy

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma support_realChartLocalize (p : M) (u : M → ℝ) :
    support (realChartLocalize (E := E) p u) ⊆ (chartAt E p) '' tsupport u := by
  intro y hy
  by_cases hy' : y ∈ (chartAt E p).target
  · refine ⟨(chartAt E p).symm y, ?_, (chartAt E p).right_inv hy'⟩
    apply subset_tsupport
    change u ((chartAt E p).symm y) ≠ 0
    change realChartLocalize (E := E) p u y ≠ 0 at hy
    simpa only [realChartLocalize, ite_eq_left hy'] using hy
  · exact False.elim (hy (by simp only [realChartLocalize, ite_eq_right hy']))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma isCompact_realChartSupport (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source) :
    IsCompact ((chartAt E p) '' tsupport u) :=
  hc.image_of_continuousOn ((chartAt E p).continuousOn.mono hs)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma tsupport_realChartLocalize (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source) :
    tsupport (realChartLocalize (E := E) p u) ⊆ (chartAt E p) '' tsupport u :=
  closure_minimal (support_realChartLocalize p u) (isCompact_realChartSupport p u hc hs).isClosed

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma hasCompactSupport_realChartLocalize (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source) :
    HasCompactSupport (realChartLocalize (E := E) p u) :=
  (isCompact_realChartSupport p u hc hs).of_isClosed_subset isClosed_closure
    (tsupport_realChartLocalize p u hc hs)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma tsupport_realChartLocalize_subset (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source) :
    tsupport (realChartLocalize (E := E) p u) ⊆ (chartAt E p).target :=
  (tsupport_realChartLocalize p u hc hs).trans
    (image_subset_iff.mpr fun _ hx => (chartAt E p).map_source (hs hx))

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma realChartLocalize_fderiv (p : M) (u : M → ℝ) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    fderiv ℝ (realChartLocalize (E := E) p u) y = fderiv ℝ (u ∘ (chartAt E p).symm) y := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(chartAt E p).open_target.mem_nhds hy] with z hz
  exact realChartLocalize_eq p u hz


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoefficientGradientApply
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

lemma metricChartIntegral_change (g : SmoothMetric E M) (p q : M) (f : M → ℝ)
    (hp : support f ⊆ (chartAt E p).source)
    (hq : support f ⊆ (chartAt E q).source) :
    metricChartIntegral g p f = metricChartIntegral g q f := by
  let e := (chartAt E q).symm.trans (chartAt E p)
  have hs : e.source ⊆ (chartAt E q).target := fun _ h => h.1
  have ht : e.target ⊆ (chartAt E p).target := fun _ h => h.1
  have hleft : metricChartIntegral g p f =
      ∫ y in e.target, Real.sqrt (metricCoefficients g p y).det * f ((chartAt E p).symm y) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (chartAt E p).open_target.measurableSet ht
    intro y hy
    have hz : f ((chartAt E p).symm y) = 0 := by
      by_contra hh
      exact hy.2 ⟨hy.1, hq hh⟩
    rw [hz, mul_zero]
  have hright : metricChartIntegral g q f =
      ∫ y in e.source, Real.sqrt (metricCoefficients g q y).det * f ((chartAt E q).symm y) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (chartAt E q).open_target.measurableSet hs
    intro y hy
    have hz : f ((chartAt E q).symm y) = 0 := by
      by_contra hh
      exact hy.2 ⟨hy.1, hp hh⟩
    rw [hz, mul_zero]
  rw [hleft, hright]
  have hd : ∀ y ∈ e.source, HasFDerivAt e (fderiv ℝ (chartTransition p q) y) y := by
    intro y hy
    exact ((contDiffAt_chartTransition p q hy.1 hy.2).differentiableAt (by simp)).hasFDerivAt
  rw [integral_target_eq_integral_abs_det_fderiv_smul volume hd]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro y hy
  dsimp only
  rw [metricDensity_change g p q hy.1 hy.2]
  have he : (chartAt E p).symm (e y) = (chartAt E q).symm y :=
    (chartAt E p).left_inv hy.2
  rw [he]
  change |(fderiv ℝ (chartTransition p q) y).toLinearMap.det| *
    (Real.sqrt (metricCoefficients g p (chartTransition p q y)).det * _) = _
  rw [coordinateTransitionMatrix, LinearMap.det_toMatrix]
  ring

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace MetricIntegralAtlas
variable (A : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

omit [T2Space M] in
lemma integral_eq_chart (q : M) (f : M →ᵇ ℝ)
    (hf : tsupport f ⊆ (chartAt E q).source) :
    A.integral g f = metricChartIntegral g q f := by
  classical
  have hc (i : A.t) : IntegrableOn (fun y => Real.sqrt (metricCoefficients g q y).det *
      (A.ρ i ((chartAt E q).symm y) * f ((chartAt E q).symm y))) (chartAt E q).target :=
    metricChart_integrable g q ((A.ρ i).property.continuous.mul f.continuous)
      (HasCompactSupport.of_compactSpace _) (tsupport_mul_subset_right.trans hf)
  unfold integral
  calc
    _ = ∑ i : A.t, metricChartIntegral g q (fun x => A.ρ i x * f x) := by
      apply Finset.sum_congr rfl
      intro i _
      apply metricChartIntegral_change
      · exact (subset_tsupport _).trans (tsupport_mul_subset_left.trans (A.subordinate i))
      · exact (subset_tsupport _).trans (tsupport_mul_subset_right.trans hf)
    _ = ∫ y in (chartAt E q).target, ∑ i : A.t,
        Real.sqrt (metricCoefficients g q y).det * (A.ρ i ((chartAt E q).symm y) *
          f ((chartAt E q).symm y)) := (integral_finsetSum _ (fun i _ => hc i)).symm
    _ = metricChartIntegral g q f := by
      apply setIntegral_congr_fun (chartAt E q).open_target.measurableSet
      intro y _
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      have hρ : ∑ i : A.t, A.ρ i ((chartAt E q).symm y) = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using A.ρ.sum_eq_one (mem_univ ((chartAt E q).symm y))
      rw [hρ, one_mul]

end MetricIntegralAtlas

end

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma realValue_inclusion (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.realValue (2 * (k : ℝ)) (A.realInclusion u) x =
      A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u x := by
  change (A.representative _ (A.inclusion u) x).re = _
  rw [A.inclusion_representative]
  rfl

omit [T2Space M] in
lemma realValue_C2 (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u) :=
  Complex.reCLM.contMDiff.comp (A.representative_C2 u)

lemma realResolvent_value (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (u : A.realH (2 * (k : ℝ))) (x : M) :
    α * A.realValue (2 * ((k + 1 : ℕ) : ℝ)) (A.realResolvent B α hα0 hα he u) x -
      laplaceBeltrami g (A.realValue (2 * ((k + 1 : ℕ) : ℝ))
        (A.realResolvent B α hα0 hα he u)) x = A.realValue (2 * (k : ℝ)) u x := by
  change α * (A.representative _ (A.resolvent B α hα he u) x).re -
      laplaceBeltrami g (fun y => (A.representative _ (A.resolvent B α hα he u) y).re) x =
        (A.representative (2 * (k : ℝ)) u.val x).re
  have h := congrArg Complex.re (A.resolvent_equation B α hα he u x)
  simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, complexLaplaceBeltrami, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero,
    add_zero, Function.comp_def] using h

end CompactMetricAtlas

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_IntegrableCompactTsupport
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
namespace YauCounterexamples
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma integrableOn_compact_tsupport {O : Set E} (hO : IsOpen O) {f : E → ℝ}
    (hf : ContinuousOn f O) (hc : HasCompactSupport f) (hs : tsupport f ⊆ O) :
    IntegrableOn f O := by
  apply IntegrableOn.of_inter_support hO.measurableSet
  exact ((hf.mono hs).integrableOn_compact hc).mono_set (fun _ hx => subset_tsupport f hx.2)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffMetricFluxC1
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
namespace YauCounterexamples
open Set Filter Manifold
open scoped Topology ContDiff Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contDiffAt_metricFlux_C1 {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    ContDiffAt ℝ 1 (fun z => metricFlux g u p z i) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  apply (hd.of_le (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top))).mul
  apply ContDiffAt.sum
  intro j _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hv := (contDiffAt_inChart_C2 hu p hy).fderiv_right (m := 1) (by norm_num)
  exact (ha.of_le (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top))).mul (hv.clm_apply contDiffAt_const)

omit [FiniteDimensional ℝ E] in
lemma contDiff_realChartLocalize_C2 (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) :
    ContDiff ℝ 2 (realChartLocalize (E := E) p u) := by
  rw [← contMDiff_iff_contDiff]
  apply contMDiff_of_tsupport
  intro y hy
  have hyt := tsupport_realChartLocalize_subset (E := E) p u hc hs hy
  rw [contMDiffAt_iff_contDiffAt]
  apply (contDiffAt_inChart_C2 hu p hyt).congr_of_eventuallyEq
  filter_upwards [(chartAt E p).open_target.mem_nhds hyt] with z hz
  exact realChartLocalize_eq p u hz
lemma localGradientPair_change_C2 {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v)
    (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    localGradientPair g u v q y = localGradientPair g u v p (chartTransition p q y) := by
  let J := coordinateTransitionMatrix p q y
  let du : CoordIndex E → ℝ := fun i =>
    fderiv ℝ (u ∘ (chartAt E p).symm) (chartTransition p q y) (Module.finBasis ℝ E i)
  let dv : CoordIndex E → ℝ := fun i =>
    fderiv ℝ (v ∘ (chartAt E p).symm) (chartTransition p q y) (Module.finBasis ℝ E i)
  have hu' : (fun i => fderiv ℝ (u ∘ (chartAt E q).symm) y (Module.finBasis ℝ E i)) =
      Jᵀ *ᵥ du := by
    ext i
    rw [fderiv_inChart_change_C2 hu p q hy hp]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, J,du, mul_comm]
  have hv' : (fun i => fderiv ℝ (v ∘ (chartAt E q).symm) y (Module.finBasis ℝ E i)) =
      Jᵀ *ᵥ dv := by
    ext i
    rw [fderiv_inChart_change_C2 hv p q hy hp]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, J,dv, mul_comm]
  have hid : J * ((metricCoefficients g q y)⁻¹ * Jᵀ) =
      (metricCoefficients g p (chartTransition p q y))⁻¹ := by
    rw [metricInverse_change_left g p q hy hp, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)),
      Matrix.one_mul]
  unfold localGradientPair
  rw [hu', hv', Matrix.mulVec_mulVec]
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hid, dotProduct_comm]

lemma coordinateGradientPair_inChart_C2 {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v)
    (g : SmoothMetric E M) (p x : M) (hx : x ∈ (chartAt E p).source) :
    coordinateGradientPair g u v x = localGradientPair g u v p ((chartAt E p) x) := by
  have he := localGradientPair_change_C2 hu hv g p x
    ((chartAt E x).map_source (mem_chart_source E x))
    (by simpa only [(chartAt E x).left_inv (mem_chart_source E x)] using hx)
  have hbase : coordinateGradientPair g u v x =
      localGradientPair g u v x ((chartAt E x) x) := by
    simp only [coordinateGradientPair, localGradientPair, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hbase, he]
  simp only [chartTransition, Function.comp_apply, (chartAt E x).left_inv (mem_chart_source E x)]

lemma contMDiff_coordinateGradientPair_C1 {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 (coordinateGradientPair g u v) := by
  have hloc (p : M) (y : E) (hy : y ∈ (chartAt E p).target) :
      ContDiffAt ℝ 1 (localGradientPair g u v p) y := by
    have hdu := (contDiffAt_inChart_C2 hu p hy).fderiv_right (m := 1) (by norm_num)
    have hdv := (contDiffAt_inChart_C2 hv p hy).fderiv_right (m := 1) (by norm_num)
    unfold localGradientPair dotProduct Matrix.mulVec
    apply ContDiffAt.sum
    intro i _
    apply (hdu.clm_apply contDiffAt_const).mul
    apply ContDiffAt.sum
    intro j _
    have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
    exact (ha.of_le (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top))).mul (hdv.clm_apply contDiffAt_const)
  intro x
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  have hx := (chartAt E x).map_source (mem_chart_source E x)
  apply (hloc x _ hx).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_target.mem_nhds hx] with y hy
  have he := coordinateGradientPair_inChart_C2 hu hv g x ((chartAt E x).symm y) ((chartAt E x).map_target hy)
  simpa only [Function.comp_apply, (chartAt E x).right_inv hy] using he
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateGradientPairScalarCorrection
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
section GradientPairCalculus
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_symm (g : SmoothMetric E M) (u v : M → ℝ) (x : M) :
    coordinateGradientPair g u v x = coordinateGradientPair g v u x := by
  have hs (i j : CoordIndex E) : (metricCoefficients g x ((chartAt E x) x))⁻¹ j i =
      (metricCoefficients g x ((chartAt E x) x))⁻¹ i j := by
    have h := congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A i j)
      (metricCoefficients_posDef g x ((chartAt E x).map_source (mem_chart_source E x))).inv.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  unfold coordinateGradientPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs]
  ring

lemma coordinateGradientPair_zero_off_support (g : SmoothMetric E M) (u v : M → ℝ)
    {x : M} (hx : x ∉ tsupport u) : coordinateGradientPair g u v x = 0 := by
  have hzero : u =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  have hc : Tendsto (chartAt E x).symm (𝓝 ((chartAt E x) x)) (𝓝 x) := by
    have hh := (chartAt E x).continuousOn_symm.continuousAt
      ((chartAt E x).open_target.mem_nhds ((chartAt E x).map_source (mem_chart_source E x)))
    simpa only [ContinuousAt, (chartAt E x).left_inv (mem_chart_source E x)] using hh
  have he : (u ∘ (chartAt E x).symm) =ᶠ[𝓝 ((chartAt E x) x)] (fun _ => (0 : ℝ)) :=
    hzero.comp_tendsto hc
  simp only [coordinateGradientPair, he.fderiv_eq, fderiv_const_apply, _root_.zero_apply,
    mul_zero, zero_mul, Finset.sum_const_zero]

lemma tsupport_coordinateGradientPair_left (g : SmoothMetric E M) (u v : M → ℝ) :
    tsupport (coordinateGradientPair g u v) ⊆ tsupport u := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  exact hx (coordinateGradientPair_zero_off_support g u v hn)

end GradientPairCalculus

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
   [CompactSpace M]
namespace MetricIntegralAtlas
variable (A : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

lemma mean_fintype_sum {ι : Type*} [Fintype ι] (f : ι → M → ℝ)
    (hf : ∀ i, Continuous (f i)) : A.mean g (fun x => ∑ i, f i x) = ∑ i, A.mean g (f i) := by
  let F (i : ι) : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f i,hf i⟩
  have he : (fun x => ∑ i, f i x) = (⇑(∑ i, F i)) := by funext x; simp [F]
  rw [he]
  change A.integralCLM g (∑ i, F i) = _
  rw [map_sum]
  rfl

lemma mean_eq_chart (p : M) (f : M → ℝ) (hf : Continuous f)
    (hs : tsupport f ⊆ (chartAt E p).source) : A.mean g f = metricChartIntegral g p f :=
  A.integral_eq_chart g p (BoundedContinuousFunction.mkOfCompact ⟨f,hf⟩) hs

end MetricIntegralAtlas

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [T2Space M] in

theorem metricChartIntegral_green_C2 (g : SmoothMetric E M) (p : M) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v)
    (huc : HasCompactSupport u) (hus : tsupport u ⊆ (chartAt E p).source) :
    metricChartIntegral g p (fun x => u x * laplaceBeltrami g v x) =
      -metricChartIntegral g p (coordinateGradientPair g u v) := by
  let f := realChartLocalize (E := E) p u
  let O := (chartAt E p).target
  let b := Module.finBasis ℝ E
  have hf : ContDiff ℝ 2 f := contDiff_realChartLocalize_C2 p u huc hus hu
  have hfc : HasCompactSupport f := hasCompactSupport_realChartLocalize p u huc hus
  have hfs : tsupport f ⊆ O := tsupport_realChartLocalize_subset p u huc hus
  have hflux (i : CoordIndex E) : ContDiffOn ℝ 1 (fun y => metricFlux g v p y i) O :=
    fun y hy => (contDiffAt_metricFlux_C1 hv g p hy i).contDiffWithinAt
  have hdf (i : CoordIndex E) : ContDiff ℝ 1 (fun y => fderiv ℝ f y (b i)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hFi (i : CoordIndex E) : IntegrableOn (fun y => f y *
      fderiv ℝ (fun z => metricFlux g v p z i) y (b i)) O := by
    apply integrableOn_compact_tsupport (chartAt E p).open_target
    · apply hf.continuous.continuousOn.mul
      intro y hy
      exact (((contDiffAt_metricFlux_C1 hv g p hy i).fderiv_right (m := 0) (by norm_num)).clm_apply
        contDiffAt_const).continuousAt.continuousWithinAt
    · exact hfc.mul_right
    · exact tsupport_mul_subset_left.trans hfs
  have hGi (i : CoordIndex E) : IntegrableOn (fun y => fderiv ℝ f y (b i) * metricFlux g v p y i) O := by
    apply integrableOn_compact_tsupport (chartAt E p).open_target
    · exact (hdf i).continuous.continuousOn.mul (hflux i).continuousOn
    · exact (hfc.fderiv_apply ℝ (b i)).mul_right
    · exact tsupport_mul_subset_left.trans ((tsupport_fderiv_apply_subset ℝ (b i)).trans hfs)
  have hleft : metricChartIntegral g p (fun x => u x * laplaceBeltrami g v x) =
      ∫ y in O, ∑ i, f y * fderiv ℝ (fun z => metricFlux g v p z i) y (b i) := by
    apply setIntegral_congr_fun (chartAt E p).open_target.measurableSet
    intro y hy
    dsimp only
    rw [laplaceBeltrami_inChart_C2 hv g p _ ((chartAt E p).map_target hy),
      (chartAt E p).right_inv hy]
    simp only [localLaplacian, ← Finset.mul_sum]
    rw [show f y = u ((chartAt E p).symm y) from realChartLocalize_eq p u hy]
    have hd : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
      (Real.sqrt_pos.2 (metricCoefficients_posDef g p hy).det_pos).ne'
    dsimp only [b]
    field_simp
  have hright : metricChartIntegral g p (coordinateGradientPair g u v) =
      ∫ y in O, ∑ i, fderiv ℝ f y (b i) * metricFlux g v p y i := by
    apply setIntegral_congr_fun (chartAt E p).open_target.measurableSet
    intro y hy
    dsimp only
    rw [coordinateGradientPair_inChart_C2 hu hv g p _ ((chartAt E p).map_target hy),
      (chartAt E p).right_inv hy]
    dsimp only [f]
    rw [realChartLocalize_fderiv p u hy]
    simp only [localGradientPair, metricFlux, Matrix.mulVec, dotProduct, Finset.mul_sum, b]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf
  rw [hleft, hright, integral_finsetSum _ (fun i _ => hFi i),
    integral_finsetSum _ (fun i _ => hGi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact local_integration_by_parts_C1 (chartAt E p).open_target (hf.of_le (by norm_num)) hfc hfs (hflux i) (b i)

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_fintype_sum_C2 {ι : Type*} [Fintype ι]
    (g : SmoothMetric E M) (f : ι → M → ℝ)
    (hf : ∀ a, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (f a)) (v : M → ℝ) (x : M) :
    coordinateGradientPair g (fun y => ∑ a, f a y) v x =
      ∑ a, coordinateGradientPair g (f a) v x := by
  have hd : fderiv ℝ ((fun y => ∑ a, f a y) ∘ (chartAt E x).symm) ((chartAt E x) x) =
      ∑ a, fderiv ℝ (f a ∘ (chartAt E x).symm) ((chartAt E x) x) :=
    fderiv_fun_sum (fun a _ => (contDiffAt_inChart_C2 (hf a) x
      ((chartAt E x).map_source (mem_chart_source E x))).differentiableAt (by simp))
  simp only [coordinateGradientPair, hd, _root_.sum_apply,
    Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ a : ι, ∑ j, (metricCoefficients g x ((chartAt E x) x))⁻¹ i j *
        fderiv ℝ (f a ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E i) *
        fderiv ℝ (v ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
   [CompactSpace M]
namespace MetricIntegralAtlas
variable (A : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

theorem green_C2 {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) :
    A.mean g (fun x => u x * laplaceBeltrami g v x) =
      -A.mean g (coordinateGradientPair g u v) := by
  let f (i : A.t) (x : M) := A.ρ i x * u x
  have hf (i : A.t) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (f i) := ((A.ρ i).property.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).mul hu
  have hs (i : A.t) : tsupport (f i) ⊆ (chartAt E (i : M)).source :=
    tsupport_mul_subset_left.trans (A.subordinate i)
  have hsum : (fun x => ∑ i : A.t, f i x) = u := by
    funext x
    dsimp only [f]
    rw [← Finset.sum_mul]
    have hρ : ∑ i : A.t, A.ρ i x = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using A.ρ.sum_eq_one (mem_univ x)
    rw [hρ, one_mul]
  calc
    _ = ∑ i : A.t, metricChartIntegral g (i : M) (fun x => f i x * laplaceBeltrami g v x) := by
      unfold mean
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      funext x
      dsimp [f]
      ring
    _ = -(∑ i : A.t, metricChartIntegral g (i : M) (coordinateGradientPair g (f i) v)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact metricChartIntegral_green_C2 g _ (hf i) hv (HasCompactSupport.of_compactSpace _) (hs i)
    _ = -(∑ i : A.t, A.mean g (coordinateGradientPair g (f i) v)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (A.mean_eq_chart g (i : M) _ (contMDiff_coordinateGradientPair_C1 (hf i) hv g).continuous
        ((tsupport_coordinateGradientPair_left g (f i) v).trans (hs i))).symm
    _ = -A.mean g (coordinateGradientPair g u v) := by
      rw [← A.mean_fintype_sum g _ (fun i => (contMDiff_coordinateGradientPair_C1 (hf i) hv g).continuous)]
      congr 2
      funext x
      rw [← coordinateGradientPair_fintype_sum_C2 g f hf v x, hsum]

theorem laplacian_symmetric_C2 {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) :
    A.mean g (fun x => u x * laplaceBeltrami g v x) =
      A.mean g (fun x => laplaceBeltrami g u x * v x) := by
  rw [A.green_C2 g hu hv]
  have he : coordinateGradientPair g u v = coordinateGradientPair g v u :=
    funext (coordinateGradientPair_symm g u v)
  rw [he, ← A.green_C2 g hv hu]
  congr 1
  funext x
  ring
end MetricIntegralAtlas

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ContinuousEigenpairLinearization
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace MetricIntegralAtlas
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)
omit [T2Space M] in
lemma mean_sub (f h : M → ℝ) (hf : Continuous f) (hh : Continuous h) :
    I.mean g (fun x => f x - h x) = I.mean g f - I.mean g h := by
  let F := BoundedContinuousFunction.mkOfCompact ⟨f,hf⟩
  let H := BoundedContinuousFunction.mkOfCompact ⟨h,hh⟩
  change I.integralCLM g (F - H) = I.integralCLM g F - I.integralCLM g H
  exact map_sub _ _ _
end MetricIntegralAtlas
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem realSpectralResolvent_symmetric_oai (I : MetricIntegralAtlas (E := E) (M := M))
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (u v : A.realH (2 * (k : ℝ))) :
    A.intrinsicForm I (2 * (k : ℝ)) (A.realSpectralResolvent B α hα0 hα he u) v =
      A.intrinsicForm I (2 * (k : ℝ)) u (A.realSpectralResolvent B α hα0 hα he v) := by
  let R := A.realResolvent B α hα0 hα he
  let U := A.realValue (2 * ((k + 1 : ℕ) : ℝ)) (R u)
  let V := A.realValue (2 * ((k + 1 : ℕ) : ℝ)) (R v)
  let f := A.realValue (2 * (k : ℝ)) u
  let h := A.realValue (2 * (k : ℝ)) v
  have hU : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 U := A.realValue_C2 _
  have hV : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 V := A.realValue_C2 _
  have hf : Continuous f := (A.realRepresentative _ u).continuous
  have hh : Continuous h := (A.realRepresentative _ v).continuous
  have heU : laplaceBeltrami g U = fun x => α * U x - f x := by
    funext x
    have hx := A.realResolvent_value B α hα0 hα he u x
    change α * U x - laplaceBeltrami g U x = f x at hx
    linarith
  have heV : laplaceBeltrami g V = fun x => α * V x - h x := by
    funext x
    have hx := A.realResolvent_value B α hα0 hα he v x
    change α * V x - laplaceBeltrami g V x = h x at hx
    linarith
  have hdU : Continuous (laplaceBeltrami g U) := by rw [heU]; exact (continuous_const.mul hU.continuous).sub hf
  have hdV : Continuous (laplaceBeltrami g V) := by rw [heV]; exact (continuous_const.mul hV.continuous).sub hh
  rw [A.intrinsicForm_apply, A.intrinsicForm_apply]
  simp only [realSpectralResolvent, ContinuousLinearMap.comp_apply, A.realValue_inclusion]
  change I.mean g (fun x => U x * h x) = I.mean g (fun x => f x * V x)
  have hleft : (fun x => U x * h x) = fun x => α * (U x * V x) - U x * laplaceBeltrami g V x := by
    funext x; rw [heV]; ring
  have hright : (fun x => f x * V x) = fun x => α * (U x * V x) - laplaceBeltrami g U x * V x := by
    funext x; rw [heU]; ring
  rw [hleft, hright, I.mean_sub g (fun x => α * (U x * V x)) (fun x => U x * laplaceBeltrami g V x)
      (continuous_const.mul (hU.continuous.mul hV.continuous)) (hU.continuous.mul hdV),
    I.mean_sub g (fun x => α * (U x * V x)) (fun x => laplaceBeltrami g U x * V x)
      (continuous_const.mul (hU.continuous.mul hV.continuous)) (hdU.mul hV.continuous),
    I.laplacian_symmetric_C2 g hU hV]
end CompactMetricAtlas

end

open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology


end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_symmetric_oai.{u_1, u_2} := @OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_symmetric_oai.{u_1, u_2}
