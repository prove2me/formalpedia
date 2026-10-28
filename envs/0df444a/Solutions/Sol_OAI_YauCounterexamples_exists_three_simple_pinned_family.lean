-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_three_simple_pinned_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:45:18.698983+00:00
-- url     : https://prove2.me/submissions/b6028d95-0016-49d5-b22a-560259b19346

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A011
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_actual_pinned_eventually_simple
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_realSpectralResolvent_compact
import Theorems.Thm_OAI_YauCounterexamples_nonempty_compactMetricAtlas
import Theorems.Thm_OAI_YauCounterexamples_three_nondegenerate_pinning_tensor

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

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma realH_closed (s : ℝ) : IsClosed (A.realH s : Set (A.H s)) := by
  change IsClosed {u | ∀ x, (A.representative s u x).im = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_eq _ continuous_const
  exact Complex.continuous_im.comp ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
    (A.representative s).continuous)

instance realH_completeSpace (s : ℝ) : CompleteSpace (A.realH s) :=
  (A.realH_closed s).completeSpace_coe

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ContinuousEigenpairLinearization
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
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

lemma compact_eigenspace_finite (T : X →L[ℝ] X) (hT : IsCompactOperator T)
    {μ : ℝ} (hμ : μ ≠ 0) : FiniteDimensional ℝ (Module.End.eigenspace T.toLinearMap μ) := by
  replace hT := hT.restrict'
    ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
      (Module.End.eigenspace_mem_invtSubmodule T.toLinearMap μ))
  rw [Module.End.restrict_eigenspace, LinearMap.coe_smul,
    IsCompactOperator.smul_iff₀ hμ] at hT
  rwa [← isCompactOperator_id_iff_finiteDimensional]

end

open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology


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

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma realSmoothRepresentativeLM_injective (s : ℝ) (ht : Module.finrank ℝ E < 2*s)
    (P : Submodule ℝ (A.realH s))
    (hf : ∀ w : P, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue s w)) :
    Injective (A.realSmoothRepresentativeLM s P hf) := by
  intro a b hab
  apply Subtype.ext
  apply A.realRepresentative_injective s ht
  ext x
  exact DFunLike.congr_fun hab x

end CompactMetricAtlas
end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem exists_three_simple_pinned_family_oai
    (I : MetricIntegralAtlas (E := ThreeModel) (M := ThreeManifold))
    (g : SmoothMetric ThreeModel ThreeManifold)
    {Λ : ℝ} (hΛ : 0<Λ) {S : Set ThreeManifold} (hS : IsOpen S)
    (u : RealSmoothFunctions ThreeModel ThreeManifold)
    (hu0 : (u : ThreeManifold → ℝ) ≠ 0)
    (hue : ∀ p, -laplaceBeltrami g u p = Λ*u p)
    (hG : ∀ p∈S, 0 < coordinateGradientPair g u u p)
    (hrank : ∃ x, (chartAt ThreeModel threeProfileCenter).symm x∈S ∧
      Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x))
    : ∃ K : pinningTensorSpace g (u : ThreeManifold → ℝ)
      S,
      ∀ᶠ t in 𝓝[≠] (0:ℝ), ∀ v : ThreeManifold → ℝ,
        ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v →
        (∀ x, -laplaceBeltrami (pinnedMetric g K.val K.property.1 t) v x =
          Λ*v x) → ∃ c : ℝ, v = fun x => c*u x := by
  classical
  have hs : Module.finrank ℝ ThreeModel < 2*(2*(2:ℝ)) := by norm_num [threeModel_finrank]
  let A := (nonempty_compactMetricAtlas g 2 hs).some
  let B : ∀ i, A.PatchCoefficients i := fun i => (A.nonempty_patchCoefficients i).some
  obtain ⟨α,hα1,hα⟩ := A.exists_parametrix_threshold B
  have hα0 : 0 < α := zero_lt_one.trans_le hα1
  let lam : ℝ := Λ
  have hla : 0 < lam := hΛ
  have hαl : α+lam ≠ 0 := ne_of_gt (add_pos hα0 hla)
  let μ : ℝ := (α+lam)⁻¹
  have hμ : μ ≠ 0 := inv_ne_zero hαl
  have hlam : μ⁻¹-α = lam := by dsimp [μ]; rw [inv_inv]; ring
  let T := A.realSpectralResolvent B α hα0 (hα α le_rfl).1 (hα α le_rfl).2
  let uz := A.realOfSmooth (2*(2:ℝ)) hs u u.contMDiff
  let P := A.intrinsicPairing I (2*(2:ℝ)) hs
  let W := Module.End.eigenspace T.toLinearMap μ ⊓ (P.form uz).ker
  let : FiniteDimensional ℝ (Module.End.eigenspace T.toLinearMap μ) :=
    compact_eigenspace_finite T (A.realSpectralResolvent_compact B α hα0 (hα α le_rfl).1 (hα α le_rfl).2) hμ
  let : FiniteDimensional ℝ W := Submodule.finiteDimensional_of_le
    (show W ≤ Module.End.eigenspace T.toLinearMap μ from inf_le_left)
  have heigen (w : W) : T w = μ • (w : A.realH (2*(2:ℝ))) :=
    Module.End.mem_eigenspace_iff.mp w.property.1
  have hf (w : W) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*(2:ℝ)) w) :=
    (A.realSpectralResolvent_eigenfunction B α hα0 (hα α le_rfl).1 (hα α le_rfl).2 hμ w (heigen w)).1
  let σ := A.realSmoothRepresentativeLM (2*(2:ℝ)) W hf
  have hσe (w : W) (x : ThreeManifold) : -laplaceBeltrami g (σ w) x = lam*σ w x := by
    have hh := (A.realSpectralResolvent_eigenfunction B α hα0 (hα α le_rfl).1 (hα α le_rfl).2 hμ w (heigen w)).2 x
    change -laplaceBeltrami g (A.realValue (2*(2:ℝ)) w) x = lam*A.realValue (2*(2:ℝ)) w x
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [hlam,Nat.cast_ofNat]
  have hp (z : A.realH (2*(2:ℝ))) : P.form uz z =
      I.mean g (fun x => u x*A.realValue (2*(2:ℝ)) z x) := by
    change I.mean g (fun x => A.realValue (2*(2:ℝ)) uz x*A.realValue (2*(2:ℝ)) z x) = _
    congr 1
    funext x
    rw [A.realOfSmooth_value]
  have hσo (w : W) : I.mean g (fun x => σ w x*u x) = 0 := by
    have hw : P.form uz w = 0 := w.property.2
    rw [hp] at hw
    convert hw using 2
    all_goals try with_reducible_and_instances rfl
    funext x
    exact mul_comm _ _
  obtain ⟨K,hK⟩ := three_nondegenerate_pinning_tensor I g hΛ hS u hue hG hrank σ
    (A.realSmoothRepresentativeLM_injective (2*(2:ℝ)) hs W hf) hσe hσo
  refine ⟨K,A.actual_pinned_eventually_simple I B α hα0 (hα α le_rfl).1 (hα α le_rfl).2
    lam hαl u u.contMDiff hu0 hue K ?_⟩
  intro z hz hzo hzz
  have hzW : z ∈ W := ⟨Module.End.mem_eigenspace_iff.mpr hz,(hp z).trans hzo⟩
  let w : W := ⟨z,hzW⟩
  have hw : w = 0 := hK.1 w (fun v => by
    change I.mean g (fun x => g.inner x (metricGradient g (A.realValue (2*(2:ℝ)) z) x)
      (K.val x (metricGradient g (A.realValue (2*(2:ℝ)) v) x))) = 0
    exact hzz v (heigen v) ((hp v).symm.trans v.property.2))
  exact congrArg Subtype.val hw
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_three_simple_pinned_family_oai := @OAI.YauCounterexamples.exists_three_simple_pinned_family_oai
