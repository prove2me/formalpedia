-- Prove2me | solution 1 for OAI.YauCounterexamples.CompactMetricAtlas.actual_simple_eigenpair_persistence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:51:56.122862+00:00
-- url     : https://prove2.me/submissions/6e16bb48-1bae-4208-877c-be67a17e5ad9

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_realSpectralResolvent_compact
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_realSpectralResolvent_symmetric
import Theorems.Thm_OAI_YauCounterexamples_nonempty_compactMetricAtlas

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
lemma χcoord_target (i : A.t) : tsupport (A.χcoord i) ⊆ (chartAt E (A.p i)).target :=
  (A.χcoord_support i).trans (A.localInverse i).in_target

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
section CoefficientOperatorContinuity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma coefficientPerturbation_tendsto_at {ι P : Type*} [Fintype ι] {l : Filter P}
    (b : ι → E) {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (a : P → ι → ι → FourierSobolevSpace E ℂ s) (c : P → ι → FourierSobolevSpace E ℂ s)
    (a₀ : ι → ι → FourierSobolevSpace E ℂ s) (c₀ : ι → FourierSobolevSpace E ℂ s)
    (ha : ∀ i j, Tendsto (fun p => a p i j) l (𝓝 (a₀ i j)))
    (hc : ∀ i, Tendsto (fun p => c p i) l (𝓝 (c₀ i))) :
    Tendsto (fun p => coefficientPerturbation b hs (a p) (c p)) l
      (𝓝 (coefficientPerturbation b hs a₀ c₀)) := by
  have hmul {f : P → FourierSobolevSpace E ℂ s} {f₀ : FourierSobolevSpace E ℂ s}
      (hf : Tendsto f l (𝓝 f₀))
      (D : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s) :
      Tendsto (fun p => (sobolevProduct hs (f p)) ∘L D) l
        (𝓝 ((sobolevProduct hs f₀) ∘L D)) := by
    have hh : Continuous (fun v : FourierSobolevSpace E ℂ s => (sobolevProduct hs v) ∘L D) := by
      fun_prop
    exact hh.continuousAt.tendsto.comp hf
  exact (tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => hmul (ha i j) _))).add
      (tendsto_finsetSum Finset.univ (fun i _ => hmul (hc i) _))
end CoefficientOperatorContinuity
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

attribute [local instance] OAI.YauCounterexamples.CompactMetricAtlas.H_nacg
attribute [local instance] OAI.YauCounterexamples.CompactMetricAtlas.H_ns
omit [T2Space M] in

theorem varyingLaplacianCLM_tendsto {P : Type*} {l : Filter P}
    (q : P → SmoothMetric E M) (q₀ : SmoothMetric E M)
    (C : ∀ p i, A.VaryingPatchCoefficients (q p) i)
    (C₀ : ∀ i, A.VaryingPatchCoefficients q₀ i)
    (ha : ∀ i j m, Tendsto (fun p => schwartzToSobolev (2 * (k : ℝ))
      (A.metricCoefficientSchwartz i ((C p i).a j m) ((C p i).smooth_a j m))) l
      (𝓝 (schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i ((C₀ i).a j m) ((C₀ i).smooth_a j m)))))
    (hc : ∀ i j, Tendsto (fun p => schwartzToSobolev (2 * (k : ℝ))
      (A.metricCoefficientSchwartz i ((C p i).c j) ((C p i).smooth_c j))) l
      (𝓝 (schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i ((C₀ i).c j) ((C₀ i).smooth_c j))))) :
    Tendsto (fun p => A.varyingLaplacianCLM (q p) (C p)) l
      (𝓝 (A.varyingLaplacianCLM q₀ C₀)) := by
  apply tendsto_finsetSum Finset.univ
  intro i _
  have hpert := coefficientPerturbation_tendsto_at (Module.finBasis ℝ E) hs _ _ _ _ (ha i) (hc i)
  have hres : Continuous (fun D : FourierSobolevSpace E ℂ (2 * (k : ℝ) + 2) →L[ℂ]
      FourierSobolevSpace E ℂ (2 * (k : ℝ)) => D.restrictScalars ℝ) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ _ _ ℝ ℝ).continuous
  have hout : Continuous (fun D : FourierSobolevSpace E ℂ (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ]
      FourierSobolevSpace E ℂ (2 * (k : ℝ)) =>
      A.lift (A.p i) (A.η i) (A.chart_η i) (A.smooth_η i) k ∘L D ∘L
        A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) (k + 1)) := by
    fun_prop
  exact hout.continuousAt.tendsto.comp (hres.continuousAt.tendsto.comp hpert)

omit [T2Space M] in
lemma varyingRealLaplacian_norm_sub_le (q q₀ : SmoothMetric E M)
    (C : ∀ i, A.VaryingPatchCoefficients q i) (C₀ : ∀ i, A.VaryingPatchCoefficients q₀ i) :
    ‖A.varyingRealLaplacian q C - A.varyingRealLaplacian q₀ C₀‖ ≤
      ‖A.varyingLaplacianCLM q C - A.varyingLaplacianCLM q₀ C₀‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (A.varyingRealLaplacian q C - A.varyingRealLaplacian q₀ C₀) (norm_nonneg _)
  intro v
  exact (A.varyingLaplacianCLM q C - A.varyingLaplacianCLM q₀ C₀).le_opNorm v.val

omit [T2Space M] in
lemma varyingRealLaplacian_tendsto {P : Type*} {l : Filter P}
    (q : P → SmoothMetric E M) (q₀ : SmoothMetric E M)
    (C : ∀ p i, A.VaryingPatchCoefficients (q p) i)
    (C₀ : ∀ i, A.VaryingPatchCoefficients q₀ i)
    (h : Tendsto (fun p => A.varyingLaplacianCLM (q p) (C p)) l
      (𝓝 (A.varyingLaplacianCLM q₀ C₀))) :
    Tendsto (fun p => A.varyingRealLaplacian (q p) (C p)) l
      (𝓝 (A.varyingRealLaplacian q₀ C₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  exact squeeze_zero (fun _ => norm_nonneg _) (fun p =>
    A.varyingRealLaplacian_norm_sub_le (q p) q₀ (C p) C₀) h

omit [T2Space M] in
lemma varyingShift_tendsto {P : Type*} {l : Filter P}
    (q : P → SmoothMetric E M) (q₀ : SmoothMetric E M)
    (C : ∀ p i, A.VaryingPatchCoefficients (q p) i)
    (C₀ : ∀ i, A.VaryingPatchCoefficients q₀ i) (α : ℝ)
    (h : Tendsto (fun p => A.varyingLaplacianCLM (q p) (C p)) l
      (𝓝 (A.varyingLaplacianCLM q₀ C₀))) :
    Tendsto (fun p => A.varyingShift (q p) (C p) α) l (𝓝 (A.varyingShift q₀ C₀ α)) :=
  tendsto_const_nhds.sub (A.varyingRealLaplacian_tendsto q q₀ C C₀ h)
end CompactMetricAtlas


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_JointMetricDet
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction SchwartzMap
namespace YauCounterexamples

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma metricCoefficientSchwartz_common_support (i : A.t) (f : E → ℝ) (hf : ContDiff ℝ ∞ f) :
    tsupport (A.metricCoefficientSchwartz i f hf) ⊆ tsupport (A.χcoord i) :=
  tsupport_mul_subset_left

omit [T2Space M] in
lemma varyingCoefficientSchwartz_a_value (q : SmoothMetric E M) (i : A.t)
    (C : A.VaryingPatchCoefficients q i) (j l : CoordIndex E) (y : E) :
    A.metricCoefficientSchwartz i (C.a j l) (C.smooth_a j l) y =
      A.χcoord i y * ((metricCoefficients q (A.p i) y)⁻¹ j l : ℂ) := by
  change A.χcoord i y * (C.a j l y : ℂ) = _
  by_cases hy : A.χcoord i y = 0
  · simp [hy]
  · rw [C.eq_a y (subset_tsupport _ hy)]

omit [T2Space M] in
lemma varyingCoefficientSchwartz_c_value (q : SmoothMetric E M) (i : A.t)
    (C : A.VaryingPatchCoefficients q i) (j : CoordIndex E) (y : E) :
    A.metricCoefficientSchwartz i (C.c j) (C.smooth_c j) y =
      A.χcoord i y * (metricFirstCoefficient q (A.p i) j y : ℂ) := by
  change A.χcoord i y * (C.c j y : ℂ) = _
  by_cases hy : A.χcoord i y = 0
  · simp [hy]
  · rw [C.eq_c y (subset_tsupport _ hy)]

end CompactMetricAtlas
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartTensorCoordLocal1
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_completeSpace _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff
variable {P E F G : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace ContinuousSmoothFamilyOn
variable {f : P → E → F} {U : Set E}
lemma value (hf : ContinuousSmoothFamilyOn f U) :
    ContinuousOn (fun z : P × E => f z.1 z.2) (univ ×ˢ U) := by
  have hc := (continuousMultilinearCurryFin0 ℝ E F).continuous.continuousOn.comp
    (hf.jets 0) (mapsTo_univ _ _)
  simpa only [Function.comp_def,continuousMultilinearCurryFin0_apply,iteratedFDeriv_zero_apply] using hc

lemma postcomp (hf : ContinuousSmoothFamilyOn f U) (g : F → G)
    (hg : ∀ p x, x ∈ U → ContDiffAt ℝ ∞ g (f p x)) :
    ContinuousSmoothFamilyOn (fun p x => g (f p x)) U := by
  classical
  refine ⟨fun p x hx => (hg p x hx).comp x (hf.smooth p x hx),fun n z hz => ?_⟩
  have hq : ∀ k, ContinuousWithinAt (fun z : P × E => iteratedFDeriv ℝ k g (f z.1 z.2))
      (univ ×ˢ U) z := fun k =>
    ((hg z.1 z.2 hz.2).continuousAt_iteratedFDeriv (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).comp_continuousWithinAt (f := fun w : P × E => f w.1 w.2) (hf.value z hz)
  have hc : ContinuousWithinAt (fun z : P × E =>
      (ftaylorSeries ℝ g (f z.1 z.2)).taylorComp (ftaylorSeries ℝ (f z.1) z.2) n)
      (univ ×ˢ U) z := by
    apply tendsto_finsetSum
    intro c _
    change ContinuousWithinAt (fun z : P × E =>
      (c.compAlongOrderedFinpartitionL ℝ E F G (iteratedFDeriv ℝ c.length g (f z.1 z.2)))
        (fun j => iteratedFDeriv ℝ (c.partSize j) (f z.1) z.2)) _ z
    exact ((c.compAlongOrderedFinpartitionL ℝ E F G).continuous.continuousAt.comp_continuousWithinAt
      (hq c.length)).eval (continuousWithinAt_pi.mpr (fun j => hf.jets (c.partSize j) z hz))
  apply hc.congr_of_eventuallyEq _ ?_
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact iteratedFDeriv_comp (hg w.1 w.2 hw.2) (hf.smooth w.1 w.2 hw.2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  · exact iteratedFDeriv_comp (hg z.1 z.2 hz.2) (hf.smooth z.1 z.2 hz.2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)

lemma prodMk {g : P → E → G} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) :
    ContinuousSmoothFamilyOn (fun p x => (f p x,g p x)) U := by
  refine ⟨fun p x hx => (hf.smooth p x hx).prodMk (hg.smooth p x hx),fun n => ?_⟩
  have hc := (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin n => E) F G).continuous.continuousOn.comp
    ((hf.jets n).prodMk (hg.jets n)) (mapsTo_univ _ _)
  apply hc.congr
  intro z hz
  exact iteratedFDeriv_prodMk (hf.smooth z.1 z.2 hz.2) (hg.smooth z.1 z.2 hz.2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)

lemma fderiv (hf : ContinuousSmoothFamilyOn f U) :
    ContinuousSmoothFamilyOn (fun p x => fderiv ℝ (f p) x) U := by
  refine ⟨fun p x hx => (hf.smooth p x hx).fderiv_right (by simp),fun n => ?_⟩
  have hc := (continuousMultilinearCurryRightEquiv' ℝ n E F).continuous.continuousOn.comp
    (hf.jets (n+1)) (mapsTo_univ _ _)
  apply hc.congr
  intro z hz
  simp only [Function.comp_apply]
  rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]

lemma const (g : E → F) (hg : ∀ x ∈ U, ContDiffAt ℝ ∞ g x) :
    ContinuousSmoothFamilyOn (fun _ : P => g) U := by
  refine ⟨fun _ => hg,fun n z hz => ?_⟩
  exact ((hg z.2 hz.2).continuousAt_iteratedFDeriv (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp_continuousWithinAt (f := Prod.snd)
    continuous_snd.continuousWithinAt

lemma scalar_const (a : P → F) (ha : Continuous a) :
    ContinuousSmoothFamilyOn (fun p (_ : E) => a p) U := by
  refine ⟨fun _ _ _ => contDiffAt_const,fun n => ?_⟩
  cases n with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E F).symm.continuous.comp (ha.comp continuous_fst) |>.continuousOn
  | succ n => simp only [iteratedFDeriv_succ_const]; exact continuousOn_const

lemma add {g : P → E → F} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) : ContinuousSmoothFamilyOn (fun p x => f p x+g p x) U :=
  (hf.prodMk hg).postcomp (fun z : F × F => z.1+z.2) (fun _ _ _ => by fun_prop)

lemma mul {f g : P → E → ℝ} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) : ContinuousSmoothFamilyOn (fun p x => f p x*g p x) U :=
  (hf.prodMk hg).postcomp (fun z : ℝ × ℝ => z.1*z.2) (fun _ _ _ => by fun_prop)

lemma inv {f : P → E → ℝ} (hf : ContinuousSmoothFamilyOn f U)
    (hn : ∀ p x, x ∈ U → f p x ≠ 0) : ContinuousSmoothFamilyOn (fun p x => (f p x)⁻¹) U :=
  hf.postcomp (fun z : ℝ => z⁻¹) (fun p x hx => contDiffAt_id.inv (hn p x hx))

lemma sqrt {f : P → E → ℝ} (hf : ContinuousSmoothFamilyOn f U)
    (hn : ∀ p x, x ∈ U → f p x ≠ 0) : ContinuousSmoothFamilyOn (fun p x => Real.sqrt (f p x)) U :=
  hf.postcomp Real.sqrt (fun p x hx => contDiffAt_id.sqrt (hn p x hx))
end ContinuousSmoothFamilyOn
end


section
open Set Filter Function Manifold
open scoped Topology ContDiff SchwartzMap
namespace ContinuousSmoothFamilyOn
variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set E}
lemma sum {ι : Type*} (s : Finset ι) (f : ι → P → E → F)
    (hf : ∀ i ∈ s, ContinuousSmoothFamilyOn (f i) U) :
    ContinuousSmoothFamilyOn (fun p x => ∑ i ∈ s, f i p x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using scalar_const (P:=P) (E:=E) (U:=U) (fun _ => (0 : F)) continuous_const
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
lemma prod {ι : Type*} (s : Finset ι) (f : ι → P → E → ℝ)
    (hf : ∀ i ∈ s, ContinuousSmoothFamilyOn (f i) U) :
    ContinuousSmoothFamilyOn (fun p x => ∏ i ∈ s, f i p x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using scalar_const (P:=P) (E:=E) (U:=U) (fun _ => (1 : ℝ)) continuous_const
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using (hf i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
lemma of_local {f : P → E → F}
    (hf : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ContinuousSmoothFamilyOn f V) :
    ContinuousSmoothFamilyOn f U := by
  constructor
  · intro p x hx
    obtain ⟨V,hV,hxV,hfV⟩ := hf x hx
    exact hfV.smooth p x hxV
  · intro n z hz
    obtain ⟨V,hV,hzV,hfV⟩ := hf z.2 hz.2
    exact ((hfV.jets n (z) ⟨mem_univ _,hzV⟩).continuousAt
      ((isOpen_univ.prod hV).mem_nhds ⟨mem_univ _,hzV⟩)).continuousWithinAt
lemma congr {f g : P → E → F} (hU : IsOpen U) (hf : ContinuousSmoothFamilyOn f U)
    (he : ∀ p, EqOn (g p) (f p) U) : ContinuousSmoothFamilyOn g U := by
  have heq (p : P) (x : E) (hx : x ∈ U) : g p =ᶠ[𝓝 x] f p :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U,hU.mem_nhds hx,he p⟩
  refine ⟨fun p x hx => (hf.smooth p x hx).congr_of_eventuallyEq (heq p x hx),fun n => ?_⟩
  apply (hf.jets n).congr
  intro z hz
  exact ((heq z.1 z.2 hz.2).iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
end ContinuousSmoothFamilyOn

section MetricFamily
variable {P E M : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (q : P → SmoothMetric E M) (p : M)
variable (hq : ∀ i j, ContinuousSmoothFamilyOn (fun t y => metricCoefficients (q t) p y i j) (chartAt E p).target)
include hq
lemma family_metricDet : ContinuousSmoothFamilyOn
    (fun t y => (metricCoefficients (q t) p y).det) (chartAt E p).target := by
  classical
  simp only [Matrix.det_apply']
  apply ContinuousSmoothFamilyOn.sum
  intro σ _
  apply (ContinuousSmoothFamilyOn.scalar_const _ continuous_const).mul
  apply ContinuousSmoothFamilyOn.prod
  intro i _
  exact hq _ _
lemma family_metricDensity : ContinuousSmoothFamilyOn
    (fun t y => Real.sqrt (metricCoefficients (q t) p y).det) (chartAt E p).target :=
  (family_metricDet q p hq).sqrt (fun t _ hy => (metricCoefficients_det_pos (q t) p hy).ne')
lemma family_metricInverse (i j : CoordIndex E) : ContinuousSmoothFamilyOn
    (fun t y => (metricCoefficients (q t) p y)⁻¹ i j) (chartAt E p).target := by
  classical
  have hadj : ContinuousSmoothFamilyOn (fun t y => (metricCoefficients (q t) p y).adjugate i j)
      (chartAt E p).target := by
    simp only [Matrix.adjugate_apply, Matrix.det_apply']
    apply ContinuousSmoothFamilyOn.sum
    intro σ _
    apply (ContinuousSmoothFamilyOn.scalar_const _ continuous_const).mul
    apply ContinuousSmoothFamilyOn.prod
    intro k _
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact ContinuousSmoothFamilyOn.scalar_const _ continuous_const
    · exact hq _ _
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact ((family_metricDet q p hq).inv (fun t y hy => (metricCoefficients_det_pos (q t) p hy).ne')).mul hadj
lemma family_metricFirstCoefficient (j : CoordIndex E) : ContinuousSmoothFamilyOn
    (fun t y => metricFirstCoefficient (q t) p j y) (chartAt E p).target := by
  apply ((family_metricDensity q p hq).inv
    (fun t y hy => (Real.sqrt_pos.mpr (metricCoefficients_det_pos (q t) p hy)).ne')).mul
  apply ContinuousSmoothFamilyOn.sum
  intro i _
  exact (((family_metricDensity q p hq).mul (family_metricInverse q p hq i j)).fderiv).postcomp
    (fun L : E →L[ℝ] ℝ => L (Module.finBasis ℝ E i)) (fun _ _ _ => by fun_prop)
end MetricFamily

variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem continuous_schwartz_common_support (f : P → 𝓢(E,F))
    (hf : ∀ n, Continuous (fun z : P × E => iteratedFDeriv ℝ n (f z.1) z.2))
    (K : Set E) (hK : IsCompact K) (hsupp : ∀ t, tsupport (f t) ⊆ K) : Continuous f := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt,(schwartz_withSeminorms ℝ E F).tendsto_nhds]
  rintro ⟨k,n⟩ ε hε
  have hj : Continuous (fun z : P × E => iteratedFDeriv ℝ n (f z.1-f t₀) z.2) := by
    have he : (fun z : P × E => iteratedFDeriv ℝ n (f z.1-f t₀) z.2) =
        (fun z : P × E => iteratedFDeriv ℝ n (f z.1) z.2-iteratedFDeriv ℝ n (f t₀) z.2) := by
      funext z
      exact iteratedFDeriv_sub_apply
        ((f z.1).smooth'.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
        ((f t₀).smooth'.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
    rw [he]
    exact (hf n).sub (((f t₀).smooth'.continuous_iteratedFDeriv (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp continuous_snd)
  have hc : Continuous (fun z : P × E => ‖z.2‖^k*‖iteratedFDeriv ℝ n (f z.1-f t₀) z.2‖) :=
    (continuous_snd.norm.pow k).mul hj.norm
  have he : ∀ᶠ t in 𝓝 t₀, ∀ x ∈ K,
      ‖x‖^k*‖iteratedFDeriv ℝ n (f t-f t₀) x‖ < ε/2 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hzero : ‖x‖^k*‖iteratedFDeriv ℝ n (f t₀-f t₀) x‖ = 0 := by simp
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa only [hzero] using half_pos hε))
  filter_upwards [he] with t ht
  simp only [SchwartzMap.schwartzSeminormFamily_apply]
  apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n (f t-f t₀) (by positivity) ?_) (half_lt_self hε)
  intro x
  by_cases hx : x ∈ K
  · exact (ht x hx).le
  · have hz : iteratedFDeriv ℝ n (f t-f t₀) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hh
      have hs := (tsupport_sub (f t) (f t₀)).trans (union_subset (hsupp t) (hsupp t₀))
      exact hx (hs (tsupport_iteratedFDeriv_subset n hh))
    simp only [hz,norm_zero,mul_zero]
    positivity
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ComplexMul
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff SchwartzMap
namespace YauCounterexamples
namespace ContinuousSmoothFamilyOn
variable {P E : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
lemma complex_mul {f g : P → E → ℂ} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) : ContinuousSmoothFamilyOn (fun p x => f p x*g p x) U :=
  (hf.prodMk hg).postcomp (fun z : ℂ × ℂ => z.1*z.2) (fun _ _ _ => by fun_prop)
lemma cutoff_complex (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ)
    {f : P → E → ℂ} (hU : IsOpen U) (hs : tsupport χ ⊆ U)
    (hf : ContinuousSmoothFamilyOn f U) :
    ContinuousSmoothFamilyOn (fun p x => χ x*f p x) univ := by
  apply of_local
  intro x hx
  by_cases hxs : x ∈ tsupport χ
  · exact ⟨U,hU,hs hxs,(const χ (fun y _ => hχ.contDiffAt)).complex_mul hf⟩
  · refine ⟨(tsupport χ)ᶜ,(isClosed_tsupport χ).isOpen_compl,hxs,?_⟩
    apply (scalar_const (fun _ : P => (0:ℂ)) continuous_const).congr (isClosed_tsupport χ).isOpen_compl
    intro p y hy
    simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]
end ContinuousSmoothFamilyOn
variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
  {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
namespace CompactMetricAtlas
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
theorem continuousFamily_varyingLaplacian_tendsto (q : P → SmoothMetric E M)
    (hq : ∀ i j l, ContinuousSmoothFamilyOn
      (fun t y => metricCoefficients (q t) (A.p i) y j l) (chartAt E (A.p i)).target)
    (C : ∀ t i, A.VaryingPatchCoefficients (q t) i) (p₀ : P) :
    Tendsto (fun t => A.varyingLaplacianCLM (q t) (C t)) (𝓝 p₀)
      (𝓝 (A.varyingLaplacianCLM (q p₀) (C p₀))) := by
  apply A.varyingLaplacianCLM_tendsto q (q p₀) C (C p₀)
  · intro i j l
    apply (schwartzToSobolev (2*(k:ℝ))).continuous.tendsto _ |>.comp
    apply Continuous.tendsto
    apply continuous_schwartz_common_support _ ?_ (tsupport (A.χcoord i)) (A.compact_χcoord i)
      (fun t => A.metricCoefficientSchwartz_common_support i _ _)
    intro n
    have he (t : P) : (A.metricCoefficientSchwartz i ((C t i).a j l) ((C t i).smooth_a j l) : E → ℂ) =
        fun y => A.χcoord i y * ((metricCoefficients (q t) (A.p i) y)⁻¹ j l : ℂ) :=
      funext (A.varyingCoefficientSchwartz_a_value (q t) i (C t i) j l)
    simp_rw [he]
    have hf := ((family_metricInverse q (A.p i) (hq i) j l).postcomp
      (fun x : ℝ => (x:ℂ)) (fun _ _ _ => Complex.ofRealCLM.contDiff.contDiffAt)).cutoff_complex
      (A.χcoord i) (A.smooth_χcoord i) (chartAt E (A.p i)).open_target (A.χcoord_target i)
    exact continuousOn_univ.mp (by simpa only [univ_prod_univ] using hf.jets n)
  · intro i j
    apply (schwartzToSobolev (2*(k:ℝ))).continuous.tendsto _ |>.comp
    apply Continuous.tendsto
    apply continuous_schwartz_common_support _ ?_ (tsupport (A.χcoord i)) (A.compact_χcoord i)
      (fun t => A.metricCoefficientSchwartz_common_support i _ _)
    intro n
    have he (t : P) : (A.metricCoefficientSchwartz i ((C t i).c j) ((C t i).smooth_c j) : E → ℂ) =
        fun y => A.χcoord i y * (metricFirstCoefficient (q t) (A.p i) j y : ℂ) :=
      funext (A.varyingCoefficientSchwartz_c_value (q t) i (C t i) j)
    simp_rw [he]
    have hf := ((family_metricFirstCoefficient q (A.p i) (hq i) j).postcomp
      (fun x : ℝ => (x:ℂ)) (fun _ _ _ => Complex.ofRealCLM.contDiff.contDiffAt)).cutoff_complex
      (A.χcoord i) (A.smooth_χcoord i) (chartAt E (A.p i)).open_target (A.χcoord_target i)
    exact continuousOn_univ.mp (by simpa only [univ_prod_univ] using hf.jets n)
end CompactMetricAtlas
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

lemma continuousAt_preconditionedInverse (R : X →L[ℝ] Y) (L : Y →L[ℝ] X)
    (h : IsUnit (L ∘L R)) : ContinuousAt (preconditionedInverse R) L := by
  have hm : Continuous (fun T : Y →L[ℝ] X => T ∘L R) := by fun_prop
  have hi : ContinuousAt Ring.inverse (L ∘L R) := by
    obtain ⟨u, hu⟩ := h
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hI : Tendsto (fun T : Y →L[ℝ] X => Ring.inverse (T ∘L R)) (𝓝 L)
      (𝓝 (Ring.inverse (L ∘L R))) := hi.tendsto.comp hm.continuousAt.tendsto
  have hout : Continuous (fun D : X →L[ℝ] X => R ∘L D) := by fun_prop
  exact hout.continuousAt.tendsto.comp hI

lemma eventuallyIsUnit_preconditioned (R : X →L[ℝ] Y) (L : Y →L[ℝ] X)
    (h : IsUnit (L ∘L R)) : ∀ᶠ T in 𝓝 L, IsUnit (T ∘L R) := by
  have hm : Continuous (fun T : Y →L[ℝ] X => T ∘L R) := by fun_prop
  exact hm.continuousAt.eventually (Units.isOpen.mem_nhds h)

lemma preconditionedInverse_tendsto {P : Type*} {l : Filter P}
    (R : X →L[ℝ] Y) (L : Y →L[ℝ] X) (h : L ∘L R = 1)
    (T : P → Y →L[ℝ] X) (hT : Tendsto T l (𝓝 L)) :
    Tendsto (fun p => preconditionedInverse R (T p)) l (𝓝 R) := by
  have hi : IsUnit (L ∘L R) := h ▸ isUnit_one
  simpa only [preconditionedInverse_base R L h, Function.comp_def] using
    (continuousAt_preconditionedInverse R L hi).tendsto.comp hT
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

namespace PositivePairing
variable (B : PositivePairing (X := X))

theorem simple_eigenvalue_complement_invertible (T : X →L[ℝ] X)
    (hT : IsCompactOperator T) (hsym : ∀ x y, B.form (T x) y = B.form x (T y))
    {μ : ℝ} (hμ : μ ≠ 0) {u : X} (hu0 : u ≠ 0) (hu : T u = μ • u)
    (hsimple : ∀ v, T v = μ • v → ∃ c : ℝ, v = c • u) :
    IsUnit (T.restrict (B.perpendicular_invariant T hsym hu) - μ • 1) := by
  let R := T.restrict (B.perpendicular_invariant T hsym hu)
  have hR : IsCompactOperator R := hT.restrict' (B.perpendicular_invariant T hsym hu)
  have hno : ¬ Module.End.HasEigenvalue R.toLinearMap μ := by
    intro he
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
    have heq : T (v : X) = μ • (v : X) := by
      have hh := Module.End.mem_eigenspace_iff.mp hv
      exact congrArg Subtype.val hh
    obtain ⟨c, hc⟩ := hsimple v heq
    have hb : B.form u (v : X) = 0 := v.property
    rw [hc, map_smul, smul_eq_mul] at hb
    have hc0 : c = 0 := (mul_eq_zero.mp hb).resolve_right (B.positive u hu0).ne'
    apply hv0
    apply Subtype.ext
    simpa only [hc0, zero_smul, Submodule.coe_zero] using hc
  have hr := (hR.hasEigenvalue_or_mem_resolventSet hμ).resolve_left hno
  rw [spectrum.mem_resolventSet_iff] at hr
  have hh : R - μ • 1 = -(algebraMap ℝ _ μ - R) := by
    rw [Algebra.algebraMap_eq_smul_one]
    abel
  rw [hh]
  exact hr.neg
end PositivePairing

end

section
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
namespace PositivePairing
variable (B : PositivePairing (X := X))

lemma eigenpairLinearization_bijective (T : X →L[ℝ] X)
    (hT : IsCompactOperator T) (hsym : ∀ x y, B.form (T x) y = B.form x (T y))
    {μ : ℝ} (hμ : μ ≠ 0) {u : X} (hu0 : u ≠ 0) (hu : T u = μ • u)
    (hsimple : ∀ v, T v = μ • v → ∃ c : ℝ, v = c • u) :
    Bijective (B.eigenpairLinearization T μ u) := by
  have hpos := B.positive u hu0
  have hφ : ∀ v, B.form u (T v - μ • v) = 0 := by
    intro v
    rw [map_sub, ← hsym, hu, map_smul, _root_.smul_apply, map_smul]
    exact sub_self _
  have hinj : Injective (B.eigenpairLinearization T μ u) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨a,v⟩ hv
    have hv1 : B.form u v = 0 := congrArg Prod.fst hv
    have hv2 : T v - μ • v - a • u = 0 := congrArg Prod.snd hv
    have hfa := congrArg (B.form u) hv2
    rw [map_sub, hφ, map_smul, map_zero, smul_eq_mul, zero_sub, neg_eq_zero] at hfa
    have ha : a = 0 := (mul_eq_zero.mp hfa).resolve_right hpos.ne'
    have he : T v = μ • v := by simpa only [ha, zero_smul, sub_zero, sub_eq_zero] using hv2
    obtain ⟨c, hc⟩ := hsimple v he
    rw [hc, map_smul, smul_eq_mul] at hv1
    have hc0 : c = 0 := (mul_eq_zero.mp hv1).resolve_right hpos.ne'
    simp [ha, hc, hc0]
  refine ⟨hinj, ?_⟩
  rintro ⟨c,y⟩
  let b := B.form u y / B.form u u
  let z : B.perpendicular u := ⟨y - b • u, by
    change B.form u (y - b • u) = 0
    rw [map_sub, map_smul, smul_eq_mul]
    dsimp [b]
    rw [div_mul_cancel₀ _ hpos.ne', sub_self]⟩
  have hi := B.simple_eigenvalue_complement_invertible T hT hsym hμ hu0 hu hsimple
  obtain ⟨w, hw⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hi).2 z
  have hw' : T (w : X) - μ • (w : X) = y - b • u := congrArg Subtype.val hw
  refine ⟨(-b, (c / B.form u u) • u + (w : X)), ?_⟩
  apply Prod.ext
  · change B.form u ((c / B.form u u) • u + (w : X)) = c
    rw [map_add, map_smul, smul_eq_mul, show B.form u (w : X) = 0 from w.property,
      add_zero, div_mul_cancel₀ _ hpos.ne']
  · change T ((c / B.form u u) • u + (w : X)) -
      μ • ((c / B.form u u) • u + (w : X)) - (-b) • u = y
    rw [map_add, map_smul, hu, smul_add, neg_smul, sub_neg_eq_add,
      smul_comm (c / B.form u u) μ u]
    have hh : μ • ((c / B.form u u) • u) + T (w : X) -
        (μ • ((c / B.form u u) • u) + μ • (w : X)) = T (w : X) - μ • (w : X) := by abel
    rw [hh, hw', sub_add_cancel]

omit [CompleteSpace X] in
lemma eigenpairDerivative_apply (T : X →L[ℝ] X) (μ : ℝ) (u : X)
    (H : X →L[ℝ] X) (b : ℝ) (v : X) :
    B.eigenpairDerivative T μ u (H,(b,v)) =
      (H,(B.form u v,T v - μ • v - b • u + H u)) := by
  simp [eigenpairDerivative, eigenpairLinearization]

lemma eigenpairDerivative_bijective (T : X →L[ℝ] X)
    (hT : IsCompactOperator T) (hsym : ∀ x y, B.form (T x) y = B.form x (T y))
    {μ : ℝ} (hμ : μ ≠ 0) {u : X} (hu0 : u ≠ 0) (hu : T u = μ • u)
    (hsimple : ∀ v, T v = μ • v → ∃ c : ℝ, v = c • u) :
    Bijective (B.eigenpairDerivative T μ u) := by
  have hL := B.eigenpairLinearization_bijective T hT hsym hμ hu0 hu hsimple
  refine ⟨?_, ?_⟩
  · rintro ⟨H,b,v⟩ ⟨K,c,w⟩ he
    simp only [B.eigenpairDerivative_apply] at he
    have hHK : H = K := congrArg Prod.fst he
    subst K
    have hvw : B.eigenpairLinearization T μ u (b,v) =
        B.eigenpairLinearization T μ u (c,w) := by
      apply Prod.ext
      · exact congrArg (fun p : EigenpairParameters (X := X) => p.2.1) he
      · exact add_right_cancel (congrArg (fun p : EigenpairParameters (X := X) => p.2.2) he)
    exact congrArg (fun p : ℝ × X => (H,p)) (hL.1 hvw)
  · rintro ⟨H,c,y⟩
    obtain ⟨⟨b,v⟩, he⟩ := hL.2 (c, y - H u)
    refine ⟨(H,(b,v)), ?_⟩
    rw [B.eigenpairDerivative_apply]
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    change B.form u v = c at he1
    change T v - μ • v - b • u = y - H u at he2
    rw [he1, he2, sub_add_cancel]

omit [CompleteSpace X] in
lemma eigenpairMap_hasStrictFDerivAt (T : X →L[ℝ] X) (μ : ℝ) (u : X) :
    HasStrictFDerivAt (B.eigenpairMap u) (B.eigenpairDerivative T μ u) (T,(μ,u)) := by
  let F := ContinuousLinearMap.fst ℝ (X →L[ℝ] X) (ℝ × X)
  let S := ContinuousLinearMap.snd ℝ (X →L[ℝ] X) (ℝ × X)
  let V := (ContinuousLinearMap.snd ℝ ℝ X).comp S
  let L := (ContinuousLinearMap.fst ℝ ℝ X).comp S
  have hh := F.hasStrictFDerivAt (x := (T,(μ,u))) |>.prodMk
    (((B.form u).hasStrictFDerivAt.comp (T,(μ,u)) V.hasStrictFDerivAt).prodMk
      ((F.hasStrictFDerivAt.clm_apply V.hasStrictFDerivAt).sub
        (L.hasStrictFDerivAt.smul V.hasStrictFDerivAt)))
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ext <;>
      simp [eigenpairDerivative, eigenpairLinearization, F,S,V,L]

theorem simple_eigenpair_persistence (T : X →L[ℝ] X)
    (hT : IsCompactOperator T) (hsym : ∀ x y, B.form (T x) y = B.form x (T y))
    {μ : ℝ} (hμ : μ ≠ 0) {u : X} (hu0 : u ≠ 0) (hu : T u = μ • u)
    (hsimple : ∀ v, T v = μ • v → ∃ c : ℝ, v = c • u) :
    ∃ (e : (X →L[ℝ] X) → ℝ) (v : (X →L[ℝ] X) → X),
      e T = μ ∧ v T = u ∧ ContinuousAt e T ∧ ContinuousAt v T ∧
      ∀ᶠ R in 𝓝 T, v R ≠ 0 ∧ R (v R) = e R • v R ∧ B.form u (v R) = B.form u u := by
  have hbij := B.eigenpairDerivative_bijective T hT hsym hμ hu0 hu hsimple
  let D := ContinuousLinearEquiv.ofBijective (B.eigenpairDerivative T μ u)
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hd : HasStrictFDerivAt (B.eigenpairMap u) (D : _ →L[ℝ] _) (T,(μ,u)) :=
    B.eigenpairMap_hasStrictFDerivAt T μ u
  let inv := hd.localInverse (B.eigenpairMap u) D (T,(μ,u))
  let z : (X →L[ℝ] X) → EigenpairParameters (X := X) := fun R => (R,(B.form u u,0))
  have hzT : z T = B.eigenpairMap u (T,(μ,u)) := by simp [z,eigenpairMap,hu]
  have hz : ContinuousAt z T := continuousAt_id.prodMk continuousAt_const
  have hval : inv (z T) = (T,(μ,u)) := by rw [hzT]; exact hd.localInverse_apply_image
  have hc : ContinuousAt (fun R => inv (z R)) T := by
    have hci : ContinuousAt inv (z T) := by
      rw [hzT]
      exact hd.localInverse_continuousAt
    exact hci.comp hz
  refine ⟨fun R => (inv (z R)).2.1, fun R => (inv (z R)).2.2,
    congrArg (fun p => p.2.1) hval, congrArg (fun p => p.2.2) hval,
    hc.snd.fst, hc.snd.snd, ?_⟩
  have he : ∀ᶠ R in 𝓝 T, B.eigenpairMap u (inv (z R)) = z R := by
    have hzt : Tendsto z (𝓝 T) (𝓝 (B.eigenpairMap u (T,(μ,u)))) := hzT ▸ hz
    exact hzt.eventually hd.eventually_right_inverse
  filter_upwards [he] with R hR
  have hR1 : (inv (z R)).1 = R := congrArg Prod.fst hR
  have hR2 : B.form u (inv (z R)).2.2 = B.form u u := congrArg (fun p => p.2.1) hR
  have hR3 : (inv (z R)).1 (inv (z R)).2.2 -
      (inv (z R)).2.1 • (inv (z R)).2.2 = 0 := congrArg (fun p => p.2.2) hR
  rw [hR1, sub_eq_zero] at hR3
  refine ⟨?_, hR3, hR2⟩
  intro hn
  rw [hn, map_zero] at hR2
  exact (B.positive u hu0).ne' hR2.symm

end PositivePairing

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

theorem varyingResolvent_tendsto {P : Type*} {l : Filter P}
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (C₀ : ∀ i, A.VaryingPatchCoefficients g i)
    (q : P → SmoothMetric E M) (C : ∀ p i, A.VaryingPatchCoefficients (q p) i)
    (hC : Tendsto (fun p => A.varyingShift (q p) (C p) α) l (𝓝 (A.varyingShift g C₀ α))) :
    (∀ᶠ p in l, IsUnit (A.varyingShift (q p) (C p) α ∘L A.realResolvent B α hα0 hα he)) ∧
      Tendsto (fun p => A.varyingResolvent B α hα0 hα he (q p) (C p)) l
        (𝓝 (A.realResolvent B α hα0 hα he)) := by
  have hb := A.varyingShift_base_comp_resolvent B α hα0 hα he C₀
  exact ⟨hC.eventually (eventuallyIsUnit_preconditioned _ _ (hb ▸ isUnit_one)),
    preconditionedInverse_tendsto _ _ hb _ hC⟩
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

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphericalSimpleEigenpairOpen
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

local instance persistence_scalarTower_r3057d7_1 (s : ℝ) : IsScalarTower ℝ ℝ (A.realH s) :=
  ⟨fun a b c => mul_smul a b c⟩
local instance (s : ℝ) : SMulCommClass ℝ ℝ (A.realH s) :=
  ⟨fun a b c => by simp only [smul_smul,mul_comm]⟩
theorem actual_simple_eigenpair_persistence_oai
    (I : MetricIntegralAtlas (E:=E) (M:=M))
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    (lam : ℝ) (hn : α+lam ≠ 0)
    (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (hue : ∀ x, -laplaceBeltrami g u x = lam*u x)
    (hsimple : ∀ v : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      (∀ x, -laplaceBeltrami g v x = lam*v x) → ∃ c : ℝ, v = fun x => c*u x)
    (q : P → SmoothMetric E M) (p₀ : P) (hq0 : q p₀ = g)
    (hq : ∀ i j l, ContinuousSmoothFamilyOn
      (fun t y => metricCoefficients (q t) (A.p i) y j l) (chartAt E (A.p i)).target) :
    ∃ (e : P → ℝ) (w : P → A.realH (2*((k+1:ℕ):ℝ))),
      e p₀ = lam ∧ A.realValue (2*((k+1:ℕ):ℝ)) (w p₀) = u ∧
      ContinuousAt e p₀ ∧ ContinuousAt w p₀ ∧
      ∀ᶠ p in 𝓝 p₀,
        ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*((k+1:ℕ):ℝ)) (w p)) ∧
        A.realValue (2*((k+1:ℕ):ℝ)) (w p) ≠ 0 ∧
        ∀ x, -laplaceBeltrami (q p) (A.realValue (2*((k+1:ℕ):ℝ)) (w p)) x =
          e p*A.realValue (2*((k+1:ℕ):ℝ)) (w p) x := by
  classical
  let C : ∀ p i, A.VaryingPatchCoefficients (q p) i := fun p i =>
    (A.nonempty_varyingPatchCoefficients (q p) i).some
  let C₀ : ∀ i, A.VaryingPatchCoefficients g i := hq0 ▸ C p₀
  have hc := A.continuousFamily_varyingLaplacian_tendsto q hq C p₀
  have hbase : A.varyingLaplacianCLM (q p₀) (C p₀) = A.varyingLaplacianCLM g C₀ := by
    subst g
    rfl
  rw [hbase] at hc
  obtain ⟨hunit,hRlim⟩ := A.varyingResolvent_tendsto B α hα0 hα he C₀ q C
    (A.varyingShift_tendsto q g C C₀ α hc)
  let R (p : P) := A.varyingResolvent B α hα0 hα he (q p) (C p)
  let R₀ := A.realResolvent B α hα0 hα he
  let T (p : P) := A.realInclusion ∘L R p
  let T₀ := A.realSpectralResolvent B α hα0 hα he
  have hR0 : R p₀ = R₀ := by
    dsimp only [R,R₀]
    subst g
    exact A.varyingResolvent_base B α hα0 hα he (C p₀)
  have hT0 : T p₀ = T₀ := congrArg (fun R => A.realInclusion ∘L R) hR0
  have hcomp : Continuous (fun R : A.realH (2*(k:ℝ)) →L[ℝ] A.realH (2*((k+1:ℕ):ℝ)) =>
      A.realInclusion ∘L R) := by fun_prop
  have hTlim : Tendsto T (𝓝 p₀) (𝓝 T₀) := hcomp.tendsto R₀ |>.comp hRlim
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
  have hueT : T₀ uz = μ • uz := A.shiftedInverse_of_smooth_eigenfunction g α hα0 R₀
    (A.realResolvent_value B α hα0 hα he) lam hn u hu hue
  have hsimpleT : ∀ z, T₀ z = μ • z → ∃ c : ℝ, z = c • uz := by
    intro z hz
    obtain ⟨hzs,hze⟩ := A.realSpectralResolvent_eigenfunction B α hα0 hα he hμ z hz
    rw [hμv] at hze
    obtain ⟨c,hc⟩ := hsimple _ hzs hze
    refine ⟨c,?_⟩
    apply A.realRepresentative_injective (2*(k:ℝ)) hs
    ext x
    change A.realValue _ z x = A.realValue _ (c • uz) x
    rw [A.realValue_smul,A.realOfSmooth_value]
    exact congrFun hc x
  obtain ⟨ev,v,hev,hv,hcev,hcv,hpair⟩ := (A.intrinsicPairing I (2*(k:ℝ)) hs).simple_eigenpair_persistence
    T₀ (A.realSpectralResolvent_compact B α hα0 hα he)
    (A.realSpectralResolvent_symmetric I B α hα0 hα he) hμ huz hueT hsimpleT
  let e (p : P) := (ev (T p))⁻¹-α
  let w (p : P) := (ev (T p))⁻¹ • R p (v (T p))
  have heT : Tendsto (fun p => ev (T p)) (𝓝 p₀) (𝓝 μ) := hev ▸ hcev.tendsto.comp hTlim
  have hvT : Tendsto (fun p => v (T p)) (𝓝 p₀) (𝓝 uz) := hv ▸ hcv.tendsto.comp hTlim
  have hinv : Tendsto (fun p => (ev (T p))⁻¹) (𝓝 p₀) (𝓝 μ⁻¹) := heT.inv₀ hμ
  have hev0 : ev (T p₀) = μ := hT0 ▸ hev
  have hv0 : v (T p₀) = uz := hT0 ▸ hv
  have hw0 (x : M) : A.realValue (2*((k+1:ℕ):ℝ)) (w p₀) x = u x := by
    dsimp only [w]
    rw [hev0,hv0,hR0,A.realValue_smul,← A.realValue_inclusion]
    change μ⁻¹*A.realValue (2*(k:ℝ)) (T₀ uz) x = u x
    rw [hueT,A.realValue_smul,A.realOfSmooth_value,← mul_assoc,inv_mul_cancel₀ hμ,one_mul]
  refine ⟨e,w,by simpa only [e,hev0] using hμv,funext hw0,?_,?_,?_⟩
  · change Tendsto e (𝓝 p₀) (𝓝 (e p₀))
    simpa only [e,hev0] using hinv.sub_const α
  · have happly := (isBoundedBilinearMap_apply (𝕜:=ℝ)
      (E:=A.realH (2*(k:ℝ))) (F:=A.realH (2*((k+1:ℕ):ℝ)))).continuous.tendsto (R₀,uz)
    have hwlim := hinv.smul (happly.comp (hRlim.prodMk_nhds hvT))
    change Tendsto w (𝓝 p₀) (𝓝 (w p₀))
    simpa only [w,hev0,hv0,hR0,Function.comp_apply,R] using hwlim
  · have hne : ∀ᶠ p in 𝓝 p₀, ev (T p) ≠ 0 := heT.eventually (isOpen_ne.mem_nhds hμ)
    filter_upwards [hunit,hTlim.eventually hpair,hne] with p hp hpv hpev
    have hshift := A.varyingResolvent_equation B α hα0 hα he (q p) (C p) hp
    obtain ⟨hsm,heig⟩ := A.shiftedInverse_eigenfunction (q p) α (R p) hshift hpev (v (T p)) hpv.2.1
    have hval : A.realValue (2*((k+1:ℕ):ℝ)) (w p) = A.realValue (2*(k:ℝ)) (v (T p)) := by
      funext x
      rw [show w p = (ev (T p))⁻¹ • R p (v (T p)) from rfl,A.realValue_smul,
        ← A.realValue_inclusion]
      change (ev (T p))⁻¹*A.realValue (2*(k:ℝ)) (T p (v (T p))) x = _
      rw [hpv.2.1,A.realValue_smul,← mul_assoc,inv_mul_cancel₀ hpev,one_mul]
    rw [hval]
    refine ⟨hsm,?_,heig⟩
    intro hz
    apply hpv.1
    apply A.realRepresentative_injective (2*(k:ℝ)) hs
    ext x
    change A.realValue _ (v (T p)) x = A.realValue _ 0 x
    rw [hz]
    simpa only [zero_smul,zero_mul,Pi.zero_apply] using
      (A.realValue_smul (2*(k:ℝ)) 0 (v (T p)) x).symm
end CompactMetricAtlas
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff BoundedContinuousFunction ENNReal NNReal

end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.YauCounterexamples.CompactMetricAtlas.actual_simple_eigenpair_persistence_oai.{u_1, u_2, u_3} := @OAI.YauCounterexamples.CompactMetricAtlas.actual_simple_eigenpair_persistence_oai.{u_1, u_2, u_3}
