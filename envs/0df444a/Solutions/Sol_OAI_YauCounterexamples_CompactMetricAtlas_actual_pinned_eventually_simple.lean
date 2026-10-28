-- Prove2me | solution 1 for OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:50:47.21303+00:00
-- url     : https://prove2.me/submissions/e1d3089a-143b-4553-8ee6-d9a6b5dac5b8

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_laplaceVariationTest_eigen_zero
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_realSpectralResolvent_compact
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_scalarTestCLM_pinned_deriv
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_smoothFamily_resolvent_tendsto
import Theorems.Thm_OAI_YauCounterexamples_nonempty_compactMetricAtlas
import Theorems.Thm_OAI_YauCounterexamples_pinnedMetric_laplacian

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LocalIntegrationParts
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contDiffAt_metricFirstCoefficient (g : SmoothMetric E M) (p : M) (j : CoordIndex E)
    {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (metricFirstCoefficient g p j) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hn : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
    (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  exact ((hd.mul ha).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold ContDiff Matrix.Norms.Elementwise
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]


theorem exists_smooth_metric_coefficients_on_compact (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).target) :
    ∃ (a : CoordIndex E → CoordIndex E → E → ℝ) (c : CoordIndex E → E → ℝ),
      (∀ i j, ContDiff ℝ ∞ (a i j)) ∧ (∀ i, ContDiff ℝ ∞ (c i)) ∧
      (∀ y ∈ K, (∀ i j, a i j y = (metricCoefficients g p y)⁻¹ i j) ∧
        (∀ i, c i y = metricFirstCoefficient g p i y)) := by
  let φ : E → Matrix (CoordIndex E) (CoordIndex E) ℝ × (CoordIndex E → ℝ) :=
    fun y => ((metricCoefficients g p y)⁻¹, fun i => metricFirstCoefficient g p i y)
  have hφ : ContDiffOn ℝ ∞ φ (chartAt E p).target := by
    apply ContDiffOn.prodMk
    · exact contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j =>
        contDiffOn_metricInverse g p i j))
    · exact contDiffOn_pi.mpr (fun i y hy =>
        (contDiffAt_metricFirstCoefficient g p i hy).contDiffWithinAt)
  obtain ⟨ψ, hψ, he⟩ := smooth_extension_near_compact hK (chartAt E p).open_target hKs hφ
  refine ⟨fun i j y => (ψ y).1 i j, fun i y => (ψ y).2 i,
    fun i j => contDiff_pi.mp (contDiff_pi.mp hψ.fst i) j,
    fun i => contDiff_pi.mp hψ.snd i, ?_⟩
  intro y hy
  have hh := he.self_of_nhdsSet hy
  exact ⟨fun i j => congrFun (congrFun (congrArg Prod.fst hh.symm) i) j,
    fun i => congrFun (congrArg Prod.snd hh.symm) i⟩


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SobolevRepresentativeOrderCongr
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma second_fderiv_const_mul_at (d : ℂ) {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => d * u z) y b) x a =
      d * fderiv ℝ (fun y => fderiv ℝ u y b) x a := by
  have he : (fun y => fderiv ℝ (fun z => d * u z) y b) =ᶠ[𝓝 x]
      (fun y => d * fderiv ℝ u y b) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    erw [fderiv_const_mul (hy.differentiableAt (by norm_num)) d]
    rfl
  rw [he.fderiv_eq]
  have hdu := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
    (differentiableAt_const b)
  erw [fderiv_const_mul hdu d]
  rfl

lemma euclideanElliptic_const_mul_at (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (d : ℂ) {u : E → ℂ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    euclideanElliptic b a c (fun y => d * u y) x = d * euclideanElliptic b a c u x := by
  simp only [euclideanElliptic, second_fderiv_const_mul_at d hu]
  erw [fderiv_const_mul (hu.differentiableAt (by norm_num)) d]
  simp only [_root_.smul_apply, smul_eq_mul, mul_left_comm _ d,
    ← Finset.mul_sum, ← mul_add]


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped SchwartzMap BoundedContinuousFunction



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ScalarCompDirectional
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
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
open Set Function Filter
open scoped Topology ContDiff
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma complex_positive_shift_kernel_eq_zero [CompactSpace M] (g : SmoothMetric E M)
    {α : ℝ} (hα : 0 < α) {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (he : ∀ x, (α : ℂ) * u x - complexLaplaceBeltrami g u x = 0) : u = 0 := by
  have hr : Complex.re ∘ u = 0 := positive_shift_kernel_eq_zero_C2 g hα
    (Complex.reCLM.contMDiff.comp hu) (fun x => by
      have h := congrArg Complex.re (he x)
      simpa [complexLaplaceBeltrami] using h)
  have hi : Complex.im ∘ u = 0 := positive_shift_kernel_eq_zero_C2 g hα
    (Complex.imCLM.contMDiff.comp hu) (fun x => by
      have h := congrArg Complex.im (he x)
      simpa [complexLaplaceBeltrami] using h)
  funext x
  apply Complex.ext
  · exact congrFun hr x
  · exact congrFun hi x


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma contMDiff_const_mul_complex {u : M → ℂ}
    {n : ℕ∞ω} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) n u) (c : ℂ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) n (fun x => c * u x) :=
  ((ContinuousLinearMap.mul ℝ ℂ) c).contMDiff.comp hu

lemma complexLaplaceBeltrami_const_mul {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u) (c : ℂ) (g : SmoothMetric E M) (x : M) :
    complexLaplaceBeltrami g (fun y => c * u y) x = c * complexLaplaceBeltrami g u x := by
  erw [complexLaplaceBeltrami_inChart (contMDiff_const_mul_complex hu c) g x
      (mem_chart_source E x), complexLaplaceBeltrami_inChart hu g x (mem_chart_source E x)]
  exact euclideanElliptic_const_mul_at _ _ _ c
    (contDiffAt_complex_inChart hu x (mem_chart_source E x))


end

open Set Filter Manifold
open scoped Topology ContDiff



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
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma nonempty_patchCoefficients (i : A.t) : Nonempty (A.PatchCoefficients i) := by
  obtain ⟨a, c, ha, hc, he⟩ := exists_smooth_metric_coefficients_on_compact g (A.p i)
    (isCompact_closedBall ((chartAt E (A.p i)) (A.p i)) (A.localInverse i).radius)
    (A.localInverse i).in_target
  exact ⟨⟨a, c, ha, hc, fun x hx => (he x (A.χcoord_support i hx)).1,
    fun x hx => (he x (A.χcoord_support i hx)).2⟩⟩

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma errorBound_tendsto (B : ∀ i, A.PatchCoefficients i) :
    Tendsto (A.errorBound B) atTop (𝓝 0) := by
  have hi (i : A.t) : Tendsto (fun α : ℝ =>
      (‖A.patchErrorTail i (B i)‖ * ((A.localInverse i).bound *
        ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖)) *
        (Real.sqrt (α * (A.localInverse i).radius ^ 2))⁻¹) atTop (𝓝 0) := by
    have hm : Tendsto (fun α : ℝ => α * (A.localInverse i).radius ^ 2) atTop atTop :=
      tendsto_id.atTop_mul_const (sq_pos_of_pos (A.localInverse i).radius_pos)
    simpa only [mul_zero, Function.comp_def] using! tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hm))
  simpa only [errorBound, Finset.sum_const_zero] using! tendsto_finsetSum Finset.univ (fun i _ => hi i)

omit [T2Space M] [CompactSpace M] in
lemma eventually_admissible : ∀ᶠ α : ℝ in atTop, ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2 := by
  apply Filter.eventually_all.mpr
  intro i
  exact (tendsto_id.atTop_mul_const (sq_pos_of_pos (A.localInverse i).radius_pos)).eventually
    (eventually_ge_atTop 1)

omit [T2Space M] in
lemma exists_parametrix_threshold (B : ∀ i, A.PatchCoefficients i) :
    ∃ a : ℝ, 1 ≤ a ∧ ∀ α ≥ a,
      (∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) ∧ A.errorBound B α ≤ 1 / 2 := by
  have he : ∀ᶠ α : ℝ in atTop, 1 ≤ α ∧
      (∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) ∧ A.errorBound B α ≤ 1 / 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), A.eventually_admissible,
      (A.errorBound_tendsto B).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with α hα ha he
    exact ⟨hα, ha, he.le⟩
  obtain ⟨a, ha⟩ := eventually_atTop.mp he
  exact ⟨a, (ha a le_rfl).1, fun α hα => (ha α hα).2⟩

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M] in
lemma complexLaplaceBeltrami_sub {u v : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 v) (g : SmoothMetric E M) (x : M) :
    complexLaplaceBeltrami g (u - v) x =
      complexLaplaceBeltrami g u x - complexLaplaceBeltrami g v x := by
  have hh : u - v = fun y => u y + (-1 : ℂ) * v y := by funext y; simp [sub_eq_add_neg]
  rw [hh, complexLaplaceBeltrami_add hu (contMDiff_const_mul_complex hv (-1)),
    complexLaplaceBeltrami_const_mul hv]
  simp [sub_eq_add_neg]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] in
lemma complex_positive_shift_solution_unique (g : SmoothMetric E M)
    {α : ℝ} (hα : 0 < α) {u v : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 v)
    (he : ∀ x, (α : ℂ) * u x - complexLaplaceBeltrami g u x =
      (α : ℂ) * v x - complexLaplaceBeltrami g v x) : u = v := by
  apply sub_eq_zero.mp
  apply complex_positive_shift_kernel_eq_zero g hα (hu.sub hv)
  intro x
  change (α : ℂ) * (u - v) x - complexLaplaceBeltrami g (u - v) x = 0
  rw [complexLaplaceBeltrami_sub hu hv, Pi.sub_apply, mul_sub]
  have h := he x
  linear_combination h

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma transfer_representative {l : ℕ} {ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))}
    (B : CompactMetricAtlas g l ht) (n : ℕ)
    (hn : Module.finrank ℝ E < 2 * (2 * (n : ℝ))) (u : A.H (2 * (n : ℝ))) :
    B.representative (2 * (n : ℝ)) (A.transfer B n u) =
      A.representative (2 * (n : ℝ)) u := by
  ext x
  simp only [transfer, sum_apply, map_sum, BoundedContinuousFunction.sum_apply,
    ContinuousLinearMap.comp_apply, B.lift_representative _ _ _ _ n hn]
  exact (manifoldSobolevRepresentative_eq_sum A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η
    A.χ A.chart_χ A.sum_η (fun i y hy => (A.one_χ i).self_of_nhdsSet hy) hn u x).symm

end CompactMetricAtlas


end

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

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M] in
lemma complexLaplaceBeltrami_ofReal (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    complexLaplaceBeltrami g (fun y => (u y : ℂ)) x = (laplaceBeltrami g u x : ℂ) := by
  apply Complex.ext
  · rfl
  · exact laplaceBeltrami_zero g x

end

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
lemma realValue_sub (s : ℝ) (u v : A.realH s) (x : M) :
    A.realValue s (u - v) x = A.realValue s u x - A.realValue s v x := by
  simp [realValue]

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

omit [T2Space M] in
lemma realOfSmooth_value (s : ℝ) (ht : Module.finrank ℝ E < 2 * s)
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    A.realValue s (A.realOfSmooth s ht f hf) x = f x := by
  dsimp only [realOfSmooth, realValue]
  erw [congrFun (A.ofSmooth_representative s ht _) x]
  rfl

end CompactMetricAtlas

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_VaryingPatchCoefficients
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
open Set Filter Function
open scoped Topology
namespace YauCounterexamples
open Set Filter Function
open scoped ContDiff Topology Manifold BoundedContinuousFunction SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma nonempty_varyingPatchCoefficients (q : SmoothMetric E M) (i : A.t) :
    Nonempty (A.VaryingPatchCoefficients q i) := by
  obtain ⟨a, c, ha, hc, he⟩ := exists_smooth_metric_coefficients_on_compact q (A.p i)
    (isCompact_closedBall ((chartAt E (A.p i)) (A.p i)) (A.localInverse i).radius)
    (A.localInverse i).in_target
  exact ⟨⟨a, c, ha, hc, fun x hx => (he x (A.χcoord_support i hx)).1,
    fun x hx => (he x (A.χcoord_support i hx)).2⟩⟩

end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CoefficientPerturbationTendsto
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
open Set Filter Function
open scoped Topology
open Set Filter Function
open scoped ContDiff Topology Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs) (q : SmoothMetric E M)

omit [T2Space M] in
lemma varyingRealLaplacian_value (B : ∀ i, A.VaryingPatchCoefficients q i)
    (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.realValue (2 * (k : ℝ)) (A.varyingRealLaplacian q B u) x =
      laplaceBeltrami q (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  change (A.representative _ (A.varyingLaplacianCLM q B u) x).re = _
  rw [A.varyingLaplacianCLM_representative]
  rfl

omit [T2Space M] in
lemma varyingShift_value (B : ∀ i, A.VaryingPatchCoefficients q i) (α : ℝ)
    (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.realValue (2 * (k : ℝ)) (A.varyingShift q B α u) x =
      α * A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u x -
        laplaceBeltrami q (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  simp only [varyingShift, sub_apply, smul_apply,
    A.realValue_sub, A.realValue_smul, A.realValue_inclusion, A.varyingRealLaplacian_value]

end CompactMetricAtlas

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff Manifold BoundedContinuousFunction SchwartzMap


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (q : ℝ → SmoothMetric E M)
variable (hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))
variable {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
include hq hu

lemma hasDerivAt_laplaceBeltrami_time (t : ℝ) (p : M) :
    HasDerivAt (fun r => laplaceBeltrami (q r) u p)
      (deriv (fun r => laplaceBeltrami (q r) u p) t) t := by
  have hh := (joint_laplaceBeltrami_chart q hq hu t p ((chartAt E p).map_source (mem_chart_source E p))).comp t
    (show ContDiffAt ℝ ∞ (fun r : ℝ => (r,chartAt E p p)) t from contDiffAt_id.prodMk contDiffAt_const)
  have hf : ContDiffAt ℝ ∞ (fun r => laplaceBeltrami (q r) u p) t := by
    simpa only [Function.comp_def, (chartAt E p).left_inv (mem_chart_source E p)] using hh
  exact (hf.differentiableAt (by simp)).hasDerivAt

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_TransferAcross
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma transferAcross_representative {g' : SmoothMetric E M} {l : ℕ}
    {ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))} (B : CompactMetricAtlas g' l ht) (n : ℕ)
    (hn : Module.finrank ℝ E < 2 * (2 * (n : ℝ))) (u : A.H (2 * (n : ℝ))) :
    B.representative (2 * (n : ℝ)) (A.transferAcross B n u) =
      A.representative (2 * (n : ℝ)) u := by
  ext x
  simp only [transferAcross, sum_apply, map_sum, BoundedContinuousFunction.sum_apply,
    ContinuousLinearMap.comp_apply, B.lift_representative _ _ _ _ n hn]
  exact (manifoldSobolevRepresentative_eq_sum A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η
    A.χ A.chart_χ A.sum_η (fun i y hy => (A.one_χ i).self_of_nhdsSet hy) hn u x).symm

omit [T2Space M] in
lemma power_representative (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (u : A.H (2 * (l : ℝ))) (n : ℕ) (x : M) :
    A.representative (2 * (l : ℝ)) (A.power l ht u n) x =
      (A.representative (2 * (l : ℝ)) u x) ^ n := by
  induction n with
  | zero =>
    change A.representative (2 * (l : ℝ))
      (A.ofSmooth (2 * (l : ℝ)) ⟨fun _ => 1, contMDiff_const⟩) x = _
    erw [A.ofSmooth_representative _ ht]
    rfl
  | succ n ih =>
    change A.representative (2 * (l : ℝ)) (A.product l ht u (A.power l ht u n)) x = _
    rw [A.product_representative l ht, ih, pow_succ']

omit [T2Space M] in
lemma polynomial_representative {N : ℕ} (l : ℕ)
    (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (a : Fin N → ManifoldSmoothFunctions E M) (u : A.H (2 * (l : ℝ))) (x : M) :
    A.representative (2 * (l : ℝ)) (A.polynomial l ht a u) x =
      ∑ i, a i x * (A.representative (2 * (l : ℝ)) u x) ^ i.val := by
  simp only [polynomial, map_sum, BoundedContinuousFunction.sum_apply,
    A.product_representative l ht, A.power_representative l ht, A.ofSmooth_representative _ ht]

theorem semilinear_regularity_step {N : ℕ} (a : Fin N → ManifoldSmoothFunctions E M) {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (he : ∀ x, complexLaplaceBeltrami g u x = ∑ i, a i x * u x ^ i.val)
    (v : A.H (2 * ((k + 1 : ℕ) : ℝ)))
    (hv : (A.representative (2 * ((k + 1 : ℕ) : ℝ)) v : M → ℂ) = u)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ))) :
    ∃ (B : CompactMetricAtlas g (k + 1) ht)
      (w : B.H (2 * ((k + 1 + 1 : ℕ) : ℝ))),
      (B.representative (2 * ((k + 1 + 1 : ℕ) : ℝ)) w : M → ℂ) = u := by
  let B := (nonempty_compactMetricAtlas g (k + 1) ht).some
  let C : ∀ i, B.PatchCoefficients i := fun i => (B.nonempty_patchCoefficients i).some
  obtain ⟨β, hβ, ha⟩ := B.exists_parametrix_threshold C
  obtain ⟨hb, hc⟩ := ha β le_rfl
  let v' := A.transfer B (k + 1) v
  let F := β • v' - B.polynomial (k + 1) ht a v'
  let w := B.resolvent C β hb hc F
  refine ⟨B, w, ?_⟩
  apply complex_positive_shift_solution_unique g (by linarith : 0 < β) (B.representative_C2 w) hu
  intro x
  rw [B.resolvent_equation]
  have hv' : (B.representative (2 * ((k + 1 : ℕ) : ℝ)) v' : M → ℂ) = u := by
    change (B.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.transfer B (k + 1) v) : M → ℂ) = u
    rw [A.transfer_representative B (k + 1) ht]
    exact hv
  simp only [F, map_sub, map_smul, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.smul_apply, Complex.real_smul,
    B.polynomial_representative (k + 1) ht, congrFun hv' x, he]

theorem represented_semilinear_solution_smooth {N : ℕ}
    (a : Fin N → ManifoldSmoothFunctions E M) {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (he : ∀ x, complexLaplaceBeltrami g u x = ∑ i, a i x * u x ^ i.val)
    (v : A.H (2 * ((k + 1 : ℕ) : ℝ)))
    (hv : (A.representative (2 * ((k + 1 : ℕ) : ℝ)) v : M → ℂ) = u) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ u := by
  have hkn (n : ℕ) : Module.finrank ℝ E < 2 * (2 * ((k + n : ℕ) : ℝ)) := by
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hrep (n : ℕ) : ∃ (B : CompactMetricAtlas g (k + n) (hkn n))
      (w : B.H (2 * ((k + n + 1 : ℕ) : ℝ))),
      (B.representative (2 * ((k + n + 1 : ℕ) : ℝ)) w : M → ℂ) = u := by
    induction n with
    | zero =>
      simp only [Nat.add_zero]
      exact ⟨A, v, hv⟩
    | succ n ih =>
      obtain ⟨B, w, hw⟩ := ih
      have ht : Module.finrank ℝ E < 2 * (2 * ((k + n + 1 : ℕ) : ℝ)) := by
        simpa only [Nat.add_assoc] using hkn (n + 1)
      convert B.semilinear_regularity_step a hu he w hw ht using 1
      all_goals try with_reducible_and_instances rfl
  apply contMDiff_infty.mpr
  intro L
  obtain ⟨B, w, hw⟩ := hrep (L + 1)
  rw [← hw]
  apply contMDiff_manifoldSobolevRepresentative B.p B.η
    (fun i => HasCompactSupport.of_compactSpace (B.η i)) B.chart_η B.smooth_η
    B.χ B.chart_χ B.smooth_χ B.sum_η
    (fun i x hx => (B.one_χ i).self_of_nhdsSet hx) L _ w
  push_cast
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  linarith

end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ClmMatrixAlgHom
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma hasDerivAt_det_exp_smul (K : Matrix ι ι ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • K)).det)
      ((NormedSpace.exp (t • K)).det * K.trace) t := by
  have hu : IsUnit (NormedSpace.exp (t • K)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (NormedSpace.isUnit_exp (t • K))
  have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ) K t
  have hd := (differentiable_det (NormedSpace.exp (t • K))).hasFDerivAt.comp_hasDerivAt t he
  erw [fderiv_det_apply _ _ hu,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hu,Matrix.mul_one] at hd
  exact hd

theorem matrix_det_exp (K : Matrix ι ι ℝ) :
    (NormedSpace.exp K).det = Real.exp K.trace := by
  let f : ℝ → ℝ := fun t => (NormedSpace.exp (t • K)).det * Real.exp (-t * K.trace)
  have hf (t : ℝ) : HasDerivAt f 0 t := by
    have hh := (hasDerivAt_det_exp_smul K t).mul
      (((hasDerivAt_id t).neg.mul_const K.trace).exp)
    convert hh using 1 <;> first | rfl | ring
  have hc := is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt)
    (fun t => (hf t).deriv) 1 0
  have hfe : (NormedSpace.exp K).det * Real.exp (-K.trace) = 1 := by
    simpa only [f,one_smul,neg_mul,one_mul,zero_smul,NormedSpace.exp_zero,Matrix.det_one,
      neg_zero,zero_mul,Real.exp_zero,mul_one] using hc
  calc (NormedSpace.exp K).det =
      (NormedSpace.exp K).det * (Real.exp (-K.trace) * Real.exp K.trace) := by
        rw [← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
    _ = Real.exp K.trace := by rw [← mul_assoc,hfe,one_mul]

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open scoped Matrix.Norms.Operator
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma clmMatrix_exp (b : Module.Basis ι ℝ E) (K : E →L[ℝ] E) :
    LinearMap.toMatrix b b (NormedSpace.exp K).toLinearMap =
      NormedSpace.exp (LinearMap.toMatrix b b K.toLinearMap) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ (E →L[ℝ] E)
  exact NormedSpace.map_exp (clmMatrixAlgHom b)
    (clmMatrixAlgHom b).toLinearMap.continuous_of_finiteDimensional K

lemma clm_det_exp (b : Module.Basis ι ℝ E) (K : E →L[ℝ] E) :
    LinearMap.det (NormedSpace.exp K).toLinearMap =
      Real.exp (LinearMap.trace ℝ E K.toLinearMap) := by
  rw [← LinearMap.det_toMatrix b,clmMatrix_exp b K,matrix_det_exp,
    LinearMap.trace_eq_matrix_trace ℝ b]

omit [FiniteDimensional ℝ E] in
lemma matrixOfForm_pullback (b : Module.Basis ι ℝ E) (G : E →L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E) :
    matrixOfForm b ((D.precomp ℝ).comp (G.comp D)) =
      (clmMatrixAlgHom b D).transpose * matrixOfForm b G * clmMatrixAlgHom b D := by
  ext i j
  change G (D (b i)) (D (b j)) =
    ((LinearMap.toMatrix b b D.toLinearMap).transpose * matrixOfForm b G *
      LinearMap.toMatrix b b D.toLinearMap) i j
  conv_lhs => arg 1; rw [← b.sum_repr (D (b i))]
  conv_lhs => arg 2; rw [← b.sum_repr (D (b j))]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,matrixOfForm,
    LinearMap.toMatrix_apply,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change (b.repr (D (b j))) k * ((b.repr (D (b i))) l * G (b l) (b k)) =
    (b.repr (D (b i))) l * G (b l) (b k) * (b.repr (D (b j))) k
  ring

theorem tracefree_exp_preserves_gram_det (b : Module.Basis ι ℝ E)
    (G : E →L[ℝ] E →L[ℝ] ℝ) (K : E →L[ℝ] E)
    (htr : LinearMap.trace ℝ E K.toLinearMap = 0) :
    (matrixOfForm b (((NormedSpace.exp K).precomp ℝ).comp
      (G.comp (NormedSpace.exp K)))).det = (matrixOfForm b G).det := by
  rw [matrixOfForm_pullback,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  have hd : (clmMatrixAlgHom b (NormedSpace.exp K)).det = 1 := by
    change (LinearMap.toMatrix b b (NormedSpace.exp K).toLinearMap).det = 1
    rw [LinearMap.det_toMatrix,clm_det_exp b K,htr,Real.exp_zero]
  rw [hd,one_mul,mul_one]


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PreconditionedInverse
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
open Set Filter Function
open scoped Topology
namespace YauCounterexamples
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [CompleteSpace X] in
lemma preconditionedInverse_right (R : X →L[ℝ] Y) (L : Y →L[ℝ] X)
    (h : IsUnit (L ∘L R)) : L ∘L preconditionedInverse R L = 1 := by
  change (L ∘L R) * Ring.inverse (L ∘L R) = 1
  exact Ring.mul_inverse_cancel _ h

omit [CompleteSpace X] in
lemma preconditionedInverse_base (R : X →L[ℝ] Y) (L : Y →L[ℝ] X)
    (h : L ∘L R = 1) : preconditionedInverse R L = R := by
  simp only [preconditionedInverse, h, Ring.inverse_one]
  rfl

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_UniformDifferenceQuotient
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology BoundedContinuousFunction
namespace YauCounterexamples
variable {X F : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem uniform_difference_quotient (f d : ℝ → X → F)
    (hd : Continuous (fun z : ℝ × X => d z.1 z.2))
    (hf : ∀ t x, HasDerivAt (fun r => f r x) (d t x) t) :
    TendstoUniformly (fun t x => t⁻¹ • (f t x-f 0 x)) (d 0) (𝓝[≠] (0 : ℝ)) := by
  let : UniformSpace X := uniformSpaceOfCompactR1
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hu := Continuous.tendstoUniformly d hd 0
  have he := (Metric.tendstoUniformly_iff.mp hu) (ε/2) (by positivity)
  obtain ⟨δ,hδ,hδe⟩ := Metric.mem_nhds_iff.mp he
  have htball : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Metric.ball 0 δ := Metric.ball_mem_nhds 0 hδ
  have ht : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ∈ Metric.ball 0 δ ∧ t ≠ 0 :=
    (htball.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  filter_upwards [ht] with t ht
  intro x
  have hder (r : ℝ) : HasDerivAt (fun r => f r x-r • d 0 x) (d r x-d 0 x) r := by
    simpa only [id_eq,one_smul,Pi.sub_apply] using! (hf r x).sub ((hasDerivAt_id r).smul_const (d 0 x))
  have hb (r : ℝ) (hr : r ∈ Metric.ball 0 δ) : ‖d r x-d 0 x‖ ≤ ε/2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hδe hr x).le
  have hm := (convex_ball (0 : ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hder r).hasDerivWithinAt) hb (Metric.mem_ball_self hδ) ht.1
  have hm' : ‖f t x-f 0 x-t • d 0 x‖ ≤ (ε/2)*‖t‖ := by
    simpa only [zero_smul, sub_zero, sub_right_comm] using hm
  have heq : t⁻¹ • (f t x-f 0 x)-d 0 x =
      t⁻¹ • (f t x-f 0 x-t • d 0 x) := by
    symm
    rw [smul_sub,smul_smul,inv_mul_cancel₀ ht.2,one_smul]
  rw [dist_eq_norm,norm_sub_rev,heq,norm_smul]
  calc
    ‖t⁻¹‖ * ‖f t x-f 0 x-t • d 0 x‖ ≤ ‖t⁻¹‖*((ε/2)*‖t‖) :=
      mul_le_mul_of_nonneg_left hm' (norm_nonneg _)
    _ = (ε/2)*(‖t‖⁻¹*‖t‖) := by rw [norm_inv]; ring
    _ = ε/2 := by rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht.2),mul_one]
    _ < ε := half_lt_self hε

theorem bounded_difference_quotient (f d : ℝ → X →ᵇ F)
    (hd : Continuous (fun z : ℝ × X => d z.1 z.2))
    (hf : ∀ t x, HasDerivAt (fun r => f r x) (d t x) t) :
    Tendsto (fun t => t⁻¹ • (f t-f 0)) (𝓝[≠] (0 : ℝ)) (𝓝 (d 0)) := by
  rw [BoundedContinuousFunction.tendsto_iff_tendstoUniformly]
  exact uniform_difference_quotient (fun t x => f t x) (fun t x => d t x) hd hf
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PinnedMetricJointGradientPair
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma pinnedMetric_inner (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) (t : ℝ)
    (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    (pinnedMetric g K hK t).inner x v w =
      g.inner x ((NormedSpace.exp ((-t/2) • (show E →L[ℝ] E from K x))) v)
        ((NormedSpace.exp ((-t/2) • (show E →L[ℝ] E from K x))) w) := rfl


end


section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma pinnedMetric_det (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    (t : ℝ) (p : M) (y : E) (hy : y ∈ (chartAt E p).target) :
    (metricCoefficients (pinnedMetric g K hK t) p y).det =
      (metricCoefficients g p y).det := by
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner ((chartAt E p).symm y)
  let A : E →L[ℝ] E := K ((chartAt E p).symm y)
  have ht : LinearMap.trace ℝ E (((-t/2) • A).toLinearMap) = 0 := by
    change LinearMap.trace ℝ E ((-t/2) • A.toLinearMap) = 0
    rw [map_smul,htr,smul_zero]
  exact tracefree_exp_preserves_gram_det (chartTangentBasis p y hy) G ((-t/2) • A) ht


end


open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff Matrix BoundedContinuousFunction

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace MetricIntegralAtlas
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

omit [CompactSpace M] [T2Space M] in
lemma mean_pinnedMetric (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    (t : ℝ) (f : M → ℝ) : I.mean (pinnedMetric g K hK t) f = I.mean g f := by
  unfold mean
  apply Finset.sum_congr rfl
  intro i _
  unfold metricChartIntegral
  apply setIntegral_congr_fun (chartAt E (i:M)).open_target.measurableSet
  intro y hy
  dsimp only
  rw [pinnedMetric_det g K hK htr t (i:M) y hy]

end MetricIntegralAtlas

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_CompactPerturbedEigenvectors
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Module
open scoped Topology
namespace YauCounterexamples
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
omit [CompleteSpace X] in
lemma compact_perturbed_eigenvectors (T : X →L[ℝ] X) (hT : IsCompactOperator T)
    (S : ℕ → X →L[ℝ] X) (hS : Tendsto S atTop (𝓝 T)) {μ : ℝ} (hμ : μ ≠ 0)
    (z : ℕ → X) (hz : ∀ n, ‖z n‖ = 1) (he : ∀ n, S n (z n) = μ • z n) :
    ∃ v : X, ‖v‖ = 1 ∧ T v = μ • v ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (z ∘ φ) atTop (𝓝 v) := by
  obtain ⟨K,hK,hKi⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y,_,φ,hφ,hy⟩ := hK.tendsto_subseq (fun n =>
    hKi ⟨z n, by simp only [Metric.mem_closedBall, dist_zero_right, hz n, le_refl], rfl⟩)
  have hd : Tendsto (fun n => (S n - T) (z n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hb (n : ℕ) : ‖(S n - T) (z n)‖ ≤ ‖S n - T‖ := by
      simpa only [hz, mul_one] using (S n - T).le_opNorm (z n)
    have hl : Tendsto (fun n => ‖S n - T‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using (hS.sub (tendsto_const_nhds (x := T))).norm
    exact squeeze_zero (fun n => norm_nonneg _) hb hl
  have hzlim : Tendsto (z ∘ φ) atTop (𝓝 (μ⁻¹ • y)) := by
    have hh := (hy.add (hd.comp hφ.tendsto_atTop)).const_smul μ⁻¹
    simp only [add_zero] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    change z (φ n) = μ⁻¹ • (T (z (φ n)) + (S (φ n) (z (φ n)) - T (z (φ n))))
    rw [he]
    have hx : T (z (φ n)) + (μ • z (φ n) - T (z (φ n))) = μ • z (φ n) := by abel
    rw [hx, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hn : ‖μ⁻¹ • y‖ = 1 := by
    apply tendsto_nhds_unique hzlim.norm
    simpa only [Function.comp_apply, hz] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hte : T (μ⁻¹ • y) = μ • (μ⁻¹ • y) := by
    have hc : Continuous (fun p : (X →L[ℝ] X) × X => p.1 p.2) := by fun_prop
    have hh := hc.tendsto (T, μ⁻¹ • y) |>.comp
      ((hS.comp hφ.tendsto_atTop).prodMk_nhds hzlim)
    have hh' := hzlim.const_smul μ
    apply tendsto_nhds_unique hh
    simpa only [Function.comp_def, he] using hh'
  exact ⟨_,hn,hte,φ,hφ,hzlim⟩

namespace PositivePairing
variable (B : PositivePairing (X := X))

omit [CompleteSpace X] in
theorem pinned_weak_first_variation (T : ℝ → X →L[ℝ] X)
    (test : X → ℝ → X →L[ℝ] ℝ) (test₀ : X → X →L[ℝ] ℝ)
    (hcompact : IsCompactOperator (T 0))
    (hT : Tendsto T (𝓝 (0 : ℝ)) (𝓝 (T 0)))
    {μ : ℝ} (hμ : μ ≠ 0) {u : X} (hu0 : u ≠ 0)
    (hu : ∀ᶠ t in 𝓝[≠] (0 : ℝ), T t u = μ • u)
    (hlim : ∀ a, T 0 a = μ • a →
      Tendsto (test a) (𝓝[≠] (0 : ℝ)) (𝓝 (test₀ a)))
    (hvan : ∀ a, T 0 a = μ • a → ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      ∀ z, T t z = μ • z → test a t z = 0)
    (hnd : ∀ z, T 0 z = μ • z → B.form u z = 0 →
      (∀ v, T 0 v = μ • v → B.form u v = 0 → test₀ v z = 0) → z = 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ z, T t z = μ • z → ∃ c : ℝ, z = c • u := by
  have hker : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ z,
      T t z = μ • z → B.form u z = 0 → z = 0 := by
    by_contra hbad
    have hf : ∃ᶠ t in 𝓝[≠] (0 : ℝ), ∃ z,
        T t z = μ • z ∧ B.form u z = 0 ∧ z ≠ 0 := by
      simpa only [not_eventually, not_forall, Classical.not_imp, exists_prop] using hbad
    obtain ⟨t,htlim,ht⟩ := exists_seq_forall_of_frequently hf
    choose z hze hzp hzn using ht
    let w : ℕ → X := fun n => ‖z n‖⁻¹ • z n
    have hwn : ∀ n, ‖w n‖ = 1 := by
      intro n
      simp only [w, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hzn n))]
    have hwe : ∀ n, T (t n) (w n) = μ • w n := by
      intro n
      simp only [w, map_smul, hze]
      exact smul_comm _ _ _
    have hwp : ∀ n, B.form u (w n) = 0 := by
      intro n
      simp only [w, map_smul, hzp, smul_zero]
    have ht0 : Tendsto t atTop (𝓝 (0 : ℝ)) := htlim.mono_right nhdsWithin_le_nhds
    obtain ⟨v,hvn,hve,φ,hφ,hv⟩ := compact_perturbed_eigenvectors (T 0) hcompact
      (T ∘ t) (hT.comp ht0) hμ w hwn hwe
    have hvp : B.form u v = 0 := by
      apply tendsto_nhds_unique ((B.form u).continuous.tendsto v |>.comp hv)
      simpa only [Function.comp_def, hwp] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have hzero : v = 0 := hnd v hve hvp (by
      intro a hae _hap
      have hc : Continuous (fun p : (X →L[ℝ] ℝ) × X => p.1 p.2) := by fun_prop
      have hdv := hc.tendsto (test₀ a,v) |>.comp
        (((hlim a hae).comp htlim |>.comp hφ.tendsto_atTop).prodMk_nhds hv)
      apply tendsto_nhds_unique hdv
      apply tendsto_const_nhds.congr'
      filter_upwards [hφ.tendsto_atTop.eventually (htlim.eventually (hvan a hae))] with j hj
      exact (hj _ (hwe (φ j))).symm)
    rw [hzero, norm_zero] at hvn
    exact zero_ne_one hvn
  filter_upwards [hker,hu] with t ht htu z hz
  let c : ℝ := B.form u z / B.form u u
  have he : T t (z - c • u) = μ • (z - c • u) := by
    simp only [map_sub, map_smul, htu, hz, smul_sub]
    rw [smul_comm c μ u]
  have hp : B.form u (z - c • u) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, c]
    rw [div_mul_cancel₀ _ (B.positive u hu0).ne', sub_self]
  exact ⟨c, sub_eq_zero.mp (ht _ he hp)⟩
end PositivePairing
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_VaryingSpectralResolventBase
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
open Set Filter Function
open scoped Topology
open Set Filter Function
open scoped ContDiff Topology Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

lemma varyingShift_base_comp_resolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (C : ∀ i, A.VaryingPatchCoefficients g i) :
    A.varyingShift g C α ∘L A.realResolvent B α hα0 hα he = 1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply A.realRepresentative_injective _ hs
  ext x
  change A.realValue _ (A.varyingShift g C α (A.realResolvent B α hα0 hα he u)) x = _
  rw [A.varyingShift_value]
  exact A.realResolvent_value B α hα0 hα he u x

lemma varyingResolvent_equation (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (q : SmoothMetric E M)
    (C : ∀ i, A.VaryingPatchCoefficients q i)
    (hunit : IsUnit (A.varyingShift q C α ∘L A.realResolvent B α hα0 hα he))
    (u : A.realH (2 * (k : ℝ))) (x : M) :
    α * A.realValue (2 * ((k + 1 : ℕ) : ℝ)) (A.varyingResolvent B α hα0 hα he q C u) x -
      laplaceBeltrami q (A.realValue (2 * ((k + 1 : ℕ) : ℝ))
        (A.varyingResolvent B α hα0 hα he q C u)) x = A.realValue (2 * (k : ℝ)) u x := by
  have hcomp : A.varyingShift q C α ∘L A.varyingResolvent B α hα0 hα he q C = 1 :=
    preconditionedInverse_right (A.realResolvent B α hα0 hα he) (A.varyingShift q C α) hunit
  have hu : A.varyingShift q C α (A.varyingResolvent B α hα0 hα he q C u) = u :=
    DFunLike.congr_fun hcomp u
  have hv := congrArg (fun v : A.realH (2 * (k : ℝ)) => A.realValue (2 * (k : ℝ)) v x) hu
  rwa [A.varyingShift_value] at hv

lemma varyingResolvent_base (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (C : ∀ i, A.VaryingPatchCoefficients g i) :
    A.varyingResolvent B α hα0 hα he g C = A.realResolvent B α hα0 hα he :=
  preconditionedInverse_base _ _ (A.varyingShift_base_comp_resolvent B α hα0 hα he C)

end CompactMetricAtlas

end

section
open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M] in
lemma laplaceBeltrami_const_mul_C2 (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u) (c : ℝ) (x : M) :
    laplaceBeltrami g (fun y => c*u y) x = c*laplaceBeltrami g u x := by
  have h := complexLaplaceBeltrami_const_mul (Complex.ofRealCLM.contMDiff.comp hu) (c : ℂ) g x
  change complexLaplaceBeltrami g (fun y => (c : ℂ)*(u y : ℂ)) x =
    (c : ℂ)*complexLaplaceBeltrami g (fun y => (u y : ℂ)) x at h
  have he : (fun y => (c : ℂ)*(u y : ℂ)) = fun y => ((c*u y : ℝ) : ℂ) := by ext y; simp
  rw [he,complexLaplaceBeltrami_ofReal,complexLaplaceBeltrami_ofReal] at h
  exact_mod_cast h

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem represented_eigenfunction_smooth (q : SmoothMetric E M) (lam : ℝ)
    (v : A.realH (2*((k+1:ℕ):ℝ)))
    (he : ∀ x, -laplaceBeltrami q (A.realValue (2*((k+1:ℕ):ℝ)) v) x =
      lam*A.realValue (2*((k+1:ℕ):ℝ)) v x) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*((k+1:ℕ):ℝ)) v) := by
  let B := (nonempty_compactMetricAtlas q k hs).some
  have ht : Module.finrank ℝ E < 2*(2*((k+1:ℕ):ℝ)) := by push_cast; linarith
  let u := A.realValue (2*((k+1:ℕ):ℝ)) v
  let w := A.transferAcross B (k+1) v
  have hw : (B.representative (2*((k+1:ℕ):ℝ)) w : M → ℂ) = fun x => (u x : ℂ) := by
    rw [show w = A.transferAcross B (k+1) v from rfl,A.transferAcross_representative B (k+1) ht]
    ext x
    exact (A.ofReal_realValue _ v x).symm
  let a : Fin 2 → ManifoldSmoothFunctions E M := fun i =>
    if i=1 then ⟨fun _ => (-lam : ℝ),contMDiff_const⟩ else 0
  have he' (x : M) : complexLaplaceBeltrami q (fun x => (u x : ℂ)) x =
      ∑ i, a i x*(u x : ℂ)^i.val := by
    rw [complexLaplaceBeltrami_ofReal]
    have hx : laplaceBeltrami q u x = -lam*u x := by linarith [he x]
    rw [hx]
    simp [a,Fin.sum_univ_succ,Fin.ext_iff]
  have hh := B.represented_semilinear_solution_smooth a
    (Complex.ofRealCLM.contMDiff.comp (A.realValue_C2 v)) he' w hw
  have hh' := Complex.reCLM.contMDiff.comp hh
  simpa only [Function.comp_def,Complex.reCLM_apply,Complex.ofRealCLM_apply,Complex.ofReal_re] using hh'

theorem shiftedInverse_eigenfunction (q : SmoothMetric E M) (α : ℝ)
    (R : A.realH (2*(k:ℝ)) →L[ℝ] A.realH (2*((k+1:ℕ):ℝ)))
    (hR : ∀ z x, α*A.realValue (2*((k+1:ℕ):ℝ)) (R z) x -
      laplaceBeltrami q (A.realValue (2*((k+1:ℕ):ℝ)) (R z)) x = A.realValue (2*(k:ℝ)) z x)
    {μ : ℝ} (hμ : μ ≠ 0) (z : A.realH (2*(k:ℝ)))
    (hz : A.realInclusion (R z) = μ • z) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*(k:ℝ)) z) ∧
    (∀ x, -laplaceBeltrami q (A.realValue (2*(k:ℝ)) z) x =
      (μ⁻¹-α)*A.realValue (2*(k:ℝ)) z x) := by
  let w := μ⁻¹ • R z
  have hw (x : M) : A.realValue (2*((k+1:ℕ):ℝ)) w x = A.realValue (2*(k:ℝ)) z x := by
    rw [show w = μ⁻¹ • R z from rfl,A.realValue_smul,← A.realValue_inclusion,hz,A.realValue_smul]
    rw [← mul_assoc,inv_mul_cancel₀ hμ,one_mul]
  have hew (x : M) : -laplaceBeltrami q (A.realValue (2*((k+1:ℕ):ℝ)) w) x =
      (μ⁻¹-α)*A.realValue (2*((k+1:ℕ):ℝ)) w x := by
    have hv : A.realValue (2*((k+1:ℕ):ℝ)) w =
        fun x => μ⁻¹*A.realValue (2*((k+1:ℕ):ℝ)) (R z) x := funext (A.realValue_smul _ _ _)
    rw [hv,laplaceBeltrami_const_mul_C2 q (A.realValue_C2 _) μ⁻¹]
    have hval : A.realValue (2*((k+1:ℕ):ℝ)) (R z) x = μ*A.realValue (2*(k:ℝ)) z x := by
      rw [← A.realValue_inclusion,hz,A.realValue_smul]
    have hinv := inv_mul_cancel₀ hμ
    have hr := hR z x
    rw [hval] at hr
    dsimp only
    rw [hval]
    have heq : laplaceBeltrami q (A.realValue (2*((k+1:ℕ):ℝ)) (R z)) x =
        α*μ*A.realValue (2*(k:ℝ)) z x - A.realValue (2*(k:ℝ)) z x := by linarith
    rw [heq]
    field_simp
    ring
  rw [funext hw] at hew
  exact ⟨(funext hw) ▸ A.represented_eigenfunction_smooth q (μ⁻¹-α) w (by simpa only [funext hw] using hew),hew⟩

theorem realSpectralResolvent_eigenfunction
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    {μ : ℝ} (hμ : μ ≠ 0) (z : A.realH (2*(k:ℝ)))
    (hz : A.realSpectralResolvent B α hα0 hα he z = μ • z) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*(k:ℝ)) z) ∧
    (∀ x, -laplaceBeltrami g (A.realValue (2*(k:ℝ)) z) x =
      (μ⁻¹-α)*A.realValue (2*(k:ℝ)) z x) :=
  A.shiftedInverse_eigenfunction g α (A.realResolvent B α hα0 hα he)
    (A.realResolvent_value B α hα0 hα he) hμ z hz

end CompactMetricAtlas
end


section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]

variable (q : ℝ → SmoothMetric E M)
variable (hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))
variable {a : M → ℝ} (ha : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ a)

omit [MeasurableSpace E] [BorelSpace E] in
lemma laplaceFamilyBCF_first_quotient :
    Tendsto (fun t => t⁻¹ • (laplaceFamilyBCF q hq ha t-laplaceFamilyBCF q hq ha 0))
      (𝓝[≠] (0 : ℝ)) (𝓝 (laplaceDerivativeBCF q hq ha 0)) :=
  bounded_difference_quotient _ _ (continuous_joint_laplaceBeltrami_time_deriv q hq ha)
    (hasDerivAt_laplaceBeltrami_time q hq ha)

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs) (I : MetricIntegralAtlas (E := E) (M := M))

lemma laplaceVariationTest_limit (s : ℝ) :
    Tendsto (A.laplaceVariationTest q hq ha I s) (𝓝[≠] (0 : ℝ))
      (𝓝 (A.scalarTestCLM I s (laplaceDerivativeBCF q hq ha 0))) :=
  (A.scalarTestCLM I s).continuous.tendsto _ |>.comp
    (laplaceFamilyBCF_first_quotient q hq ha)

end CompactMetricAtlas
end


section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
omit [MeasurableSpace E] [BorelSpace E] [T2Space M] in
lemma real_positive_shift_solution_unique (g : SmoothMetric E M)
    {α : ℝ} (hα : 0 < α) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 v)
    (he : ∀ x, α*u x-laplaceBeltrami g u x = α*v x-laplaceBeltrami g v x) : u = v := by
  have hh : (fun x => (u x : ℂ)) = fun x => (v x : ℂ) :=
    complex_positive_shift_solution_unique g hα (Complex.ofRealCLM.contMDiff.comp hu)
      (Complex.ofRealCLM.contMDiff.comp hv) (by
        intro x
        rw [complexLaplaceBeltrami_ofReal,complexLaplaceBeltrami_ofReal]
        exact_mod_cast he x)
  funext x
  exact Complex.ofReal_injective (congrFun hh x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompactSpace M] [T2Space M] in
lemma smoothMetric_eq_of_inner_eq (g h : SmoothMetric E M) (he : g.inner = h.inner) : g = h := by
  cases g
  cases h
  cases he
  rfl

omit [MeasurableSpace E] [BorelSpace E] [CompactSpace M] [T2Space M] in
lemma pinnedMetric_at_zero (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) : pinnedMetric g K hK 0 = g := by
  have hh : (pinnedMetric g K hK 0).inner = g.inner := by
    funext x
    ext a b
    simp only [pinnedMetric_inner, neg_zero, zero_div]
    erw [zero_smul, NormedSpace.exp_zero]
    rfl
  exact smoothMetric_eq_of_inner_eq _ _ hh

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
theorem shiftedInverse_of_smooth_eigenfunction (q : SmoothMetric E M) (α : ℝ) (hα : 0 < α)
    (R : A.realH (2*(k:ℝ)) →L[ℝ] A.realH (2*((k+1:ℕ):ℝ)))
    (hR : ∀ z x, α*A.realValue (2*((k+1:ℕ):ℝ)) (R z) x -
      laplaceBeltrami q (A.realValue (2*((k+1:ℕ):ℝ)) (R z)) x = A.realValue (2*(k:ℝ)) z x)
    (lam : ℝ) (hn : α+lam ≠ 0) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (he : ∀ x, -laplaceBeltrami q u x = lam*u x) :
    A.realInclusion (R (A.realOfSmooth (2*(k:ℝ)) hs u hu)) =
      (α+lam)⁻¹ • A.realOfSmooth (2*(k:ℝ)) hs u hu := by
  let z := A.realOfSmooth (2*(k:ℝ)) hs u hu
  have hv : A.realValue (2*((k+1:ℕ):ℝ)) (R z) = fun x => (α+lam)⁻¹*u x := by
    apply real_positive_shift_solution_unique q hα (A.realValue_C2 (R z))
      (contMDiff_const.mul (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)))
    intro x
    rw [hR,A.realOfSmooth_value]
    change u x = α*((α+lam)⁻¹*u x)-laplaceBeltrami q (fun y => (α+lam)⁻¹*u y) x
    rw [laplaceBeltrami_const_mul_C2 q
      (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    have hx : laplaceBeltrami q u x = -lam*u x := by linarith [he x]
    rw [hx]
    field_simp
    ring
  apply A.realRepresentative_injective (2*(k:ℝ)) hs
  ext x
  change A.realValue _ (A.realInclusion (R z)) x = A.realValue _ ((α+lam)⁻¹ • z) x
  rw [A.realValue_inclusion,A.realValue_smul,A.realOfSmooth_value]
  exact congrFun hv x

end CompactMetricAtlas
end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)
lemma varyingSpectralResolvent_base
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    (C : ∀ i, A.VaryingPatchCoefficients g i) :
    A.varyingSpectralResolvent B α hα0 hα he g C = A.realSpectralResolvent B α hα0 hα he := by
  unfold varyingSpectralResolvent realSpectralResolvent
  rw [A.varyingResolvent_base]

lemma varyingSpectralResolvent_eq_base
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    (q : SmoothMetric E M) (hq : q = g) (C : ∀ i, A.VaryingPatchCoefficients q i) :
    A.varyingSpectralResolvent B α hα0 hα he q C = A.realSpectralResolvent B α hα0 hα he := by
  subst q
  exact A.varyingSpectralResolvent_base B α hα0 hα he C

theorem actual_pinned_eventually_simple_oai
    (I : MetricIntegralAtlas (E := E) (M := M))
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    (lam : ℝ) (hn : α+lam ≠ 0)
    (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (hue : ∀ x, -laplaceBeltrami g u x = lam*u x)
    {U : Set M} (K : pinningTensorSpace g u U)
    (hnd : ∀ z : A.realH (2*(k:ℝ)),
      A.realSpectralResolvent B α hα0 hα he z = (α+lam)⁻¹ • z →
      I.mean g (fun x => u x*A.realValue (2*(k:ℝ)) z x) = 0 →
      (∀ a : A.realH (2*(k:ℝ)),
        A.realSpectralResolvent B α hα0 hα he a = (α+lam)⁻¹ • a →
        I.mean g (fun x => u x*A.realValue (2*(k:ℝ)) a x) = 0 →
        I.mean g (fun x => g.inner x (metricGradient g (A.realValue (2*(k:ℝ)) z) x)
          (K.val x (metricGradient g (A.realValue (2*(k:ℝ)) a) x))) = 0) → z = 0) :
    ∀ᶠ t in 𝓝[≠] (0:ℝ), ∀ v : M → ℝ,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      (∀ x, -laplaceBeltrami (pinnedMetric g K.val K.property.1 t) v x = lam*v x) →
      ∃ c : ℝ, v = fun x => c*u x := by
  classical
  let q := pinnedMetric g K.val K.property.1
  have hq0 : q 0 = g := pinnedMetric_at_zero g K.val K.property.1
  have hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
      ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y) :=
    fun p t y hy i j => pinnedMetric_joint_coefficients g K.val K.property.1 p i j t hy
  let C : ∀ t i, A.VaryingPatchCoefficients (q t) i := fun t i =>
    (A.nonempty_varyingPatchCoefficients (q t) i).some
  let T (t : ℝ) := A.varyingSpectralResolvent B α hα0 hα he (q t) (C t)
  let T₀ := A.realSpectralResolvent B α hα0 hα he
  have hT0 : T 0 = T₀ := by
    dsimp only [T,T₀]
    exact A.varyingSpectralResolvent_eq_base B α hα0 hα he (q 0) hq0 (C 0)
  obtain ⟨hunit,hlim⟩ := A.smoothFamily_resolvent_tendsto B α hα0 hα he q hq0
    (fun i => hq (A.p i)) C
  have hT : Tendsto T (𝓝 (0:ℝ)) (𝓝 (T 0)) := hT0.symm ▸ hlim
  let μ := (α+lam)⁻¹
  have hμ : μ ≠ 0 := inv_ne_zero hn
  have hμv : μ⁻¹-α = lam := by dsimp [μ]; rw [inv_inv]; ring
  let uz := A.realOfSmooth (2*(k:ℝ)) hs u hu
  have huz : uz ≠ 0 := by
    intro hz
    apply hu0
    funext x
    have hh := congrArg (fun z => A.realValue (2*(k:ℝ)) z x) hz
    have hzv : A.realValue (2*(k:ℝ)) 0 x = 0 := by
      simpa only [zero_smul,zero_mul] using A.realValue_smul (2*(k:ℝ)) 0 uz x
    simpa only [uz,A.realOfSmooth_value,hzv,Pi.zero_apply] using hh
  have hbase (a : A.realH (2*(k:ℝ))) (ha : T₀ a = μ • a) :
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*(k:ℝ)) a) ∧
      ∀ x, -laplaceBeltrami g (A.realValue (2*(k:ℝ)) a) x = lam*A.realValue (2*(k:ℝ)) a x := by
    have hh := A.realSpectralResolvent_eigenfunction B α hα0 hα he hμ a ha
    simpa only [hμv] using hh
  let sa (a : A.realH (2*(k:ℝ))) : RealSmoothFunctions E M :=
    if ha : T₀ a = μ • a then ⟨A.realValue (2*(k:ℝ)) a,(hbase a ha).1⟩ else 0
  have hsa (a : A.realH (2*(k:ℝ))) (ha : T₀ a = μ • a) :
      (sa a : M → ℝ) = A.realValue (2*(k:ℝ)) a := by
    have hh : sa a = ⟨A.realValue (2*(k:ℝ)) a, (hbase a ha).1⟩ := dite_eq_left ha
    exact congrArg (fun f : RealSmoothFunctions E M => (f : M → ℝ)) hh
  let test (a : A.realH (2*(k:ℝ))) := A.laplaceVariationTest q hq (sa a).contMDiff I (2*(k:ℝ))
  let test₀ (a : A.realH (2*(k:ℝ))) := A.scalarTestCLM I (2*(k:ℝ))
    (laplaceDerivativeBCF q hq (sa a).contMDiff 0)
  let P := A.intrinsicPairing I (2*(k:ℝ)) hs
  have hp (z : A.realH (2*(k:ℝ))) :
      P.form uz z = I.mean g (fun x => u x*A.realValue (2*(k:ℝ)) z x) := by
    change I.mean g (fun x => A.realValue (2*(k:ℝ)) uz x*A.realValue (2*(k:ℝ)) z x) = _
    congr 1
    funext x
    rw [A.realOfSmooth_value]
  have hueT : ∀ᶠ t in 𝓝[≠] (0:ℝ), T t uz = μ • uz := by
    filter_upwards [hunit.filter_mono nhdsWithin_le_nhds] with t ht
    exact A.shiftedInverse_of_smooth_eigenfunction (q t) α hα0
      (A.varyingResolvent B α hα0 hα he (q t) (C t))
      (A.varyingResolvent_equation B α hα0 hα he (q t) (C t) ht) lam hn u hu
      (fun x => (congrArg Neg.neg (pinnedMetric_laplacian g K.val K.property.1
        K.property.2.1 K.property.2.2.1 hu K.property.2.2.2.1 t x)).trans (hue x))
  have hvan : ∀ a, T 0 a = μ • a → ∀ᶠ t in 𝓝[≠] (0:ℝ),
      ∀ z, T t z = μ • z → test a t z = 0 := by
    intro a ha
    have ha' : T₀ a = μ • a := hT0 ▸ ha
    filter_upwards [hunit.filter_mono nhdsWithin_le_nhds] with t ht z hz
    have hzz := A.shiftedInverse_eigenfunction (q t) α
      (A.varyingResolvent B α hα0 hα he (q t) (C t))
      (A.varyingResolvent_equation B α hα0 hα he (q t) (C t) ht) hμ z hz
    rw [hμv] at hzz
    exact A.laplaceVariationTest_eigen_zero q hq (sa a).contMDiff I (2*(k:ℝ)) t hq0
      (I.mean_pinnedMetric g K.val K.property.1 K.property.2.2.1 t) z hzz.1 lam
      (by rw [hsa a ha']; exact (hbase a ha').2) hzz.2
  have hpin := P.pinned_weak_first_variation T test test₀
    (hT0.symm ▸ A.realSpectralResolvent_compact B α hα0 hα he) hT hμ huz hueT
    (fun a _ => A.laplaceVariationTest_limit q hq (sa a).contMDiff I (2*(k:ℝ))) hvan
    (by
      intro z hz hzp hab
      have hz' : T₀ z = μ • z := hT0 ▸ hz
      apply hnd z hz' ((hp z) ▸ hzp)
      intro a ha hap
      have hh := hab a (hT0.symm ▸ ha) ((hp a).symm ▸ hap)
      have heq := A.scalarTestCLM_pinned_deriv I K (sa a).contMDiff (2*(k:ℝ)) z (hbase z hz').1
      change test₀ a z = _ at heq
      rw [heq,hsa a ha] at hh
      exact neg_eq_zero.mp hh)
  filter_upwards [hpin,hunit.filter_mono nhdsWithin_le_nhds] with t ht hi v hv hve
  let vz := A.realOfSmooth (2*(k:ℝ)) hs v hv
  have hveT : T t vz = μ • vz := A.shiftedInverse_of_smooth_eigenfunction (q t) α hα0
    (A.varyingResolvent B α hα0 hα he (q t) (C t))
    (A.varyingResolvent_equation B α hα0 hα he (q t) (C t) hi) lam hn v hv hve
  obtain ⟨c,hc⟩ := ht vz hveT
  refine ⟨c,?_⟩
  funext x
  have hh := congrArg (fun z => A.realValue (2*(k:ℝ)) z x) hc
  simpa only [vz,uz,A.realValue_smul,A.realOfSmooth_value] using hh
end CompactMetricAtlas

end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple_oai.{u_1, u_2} := @OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple_oai.{u_1, u_2}
