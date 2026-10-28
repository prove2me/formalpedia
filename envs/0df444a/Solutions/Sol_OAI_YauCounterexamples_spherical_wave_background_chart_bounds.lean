-- Prove2me | solution 1 for OAI.YauCounterexamples.spherical_wave_background_chart_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:48:50.223767+00:00
-- url     : https://prove2.me/submissions/4c3ed2b1-843b-4902-b3f7-13a1485e7ca9

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A008
import Definitions.Def_OAIQ070A009
import Theorems.Thm_OAI_YauCounterexamples_roundPower_global_profile_residual_rapid_decay

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
open Set Filter Manifold BoxIntegral Metric
open scoped Topology ContDiff InnerProductSpace

lemma sphericalRadius_nonneg (a b : Euclidean 4) (q : Sphere 3) :
    0 ≤ sphericalRadius a b q := Real.sqrt_nonneg _

lemma sphericalRadius_sq (a b : Euclidean 4) (q : Sphere 3) :
    (sphericalRadius a b q)^2 =
      (inner ℝ a (q : Euclidean 4))^2+(inner ℝ b (q : Euclidean 4))^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma source_axes_orthonormal : inner ℝ sourceAxisOne sourceAxisOne = 1 ∧
    inner ℝ sourceAxisTwo sourceAxisTwo = 1 ∧ inner ℝ sourceAxisOne sourceAxisTwo = 0 := by
  norm_num [sourceAxisOne,sourceAxisTwo,EuclideanSpace.inner_single_left,PiLp.single_apply]


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
variable {n : ℕ}

section Planar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma planarLinear_apply (a b x : E) :
    planarLinear a b x = (inner ℝ a x : ℂ) + Complex.I * (inner ℝ b x : ℂ) := by
  rfl
end Planar



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LocalIntegrationParts
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
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

lemma roundPlanarChart_smooth (a b : Euclidean (d+1)) (p : Sphere d) :
    ContDiffOn ℝ ∞ (roundPlanarChart a b p) (chartAt (Euclidean d) p).target := by
  have hs : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℂ) ∞
      (fun q : Sphere d => planarLinear a b (q : Euclidean (d+1))) :=
    (planarLinear a b).contDiff.contMDiff.comp contMDiff_coe_sphere
  intro y hy
  exact (contMDiffAt_iff_contDiffAt.mp (hs.contMDiffAt.comp y
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy))).contDiffWithinAt

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SmoothExtension
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
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
namespace YauCounterexamples

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

lemma smooth_extension_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f O) :
    ∃ F : E → F, ContDiff ℝ ∞ F ∧ f =ᶠ[𝓝 x] F := by
  obtain ⟨F,hF,he⟩ := smooth_extension_near_compact isCompact_singleton hO
    (singleton_subset_iff.mpr hx) hf
  exact ⟨F,hF,he.filter_mono (nhds_le_nhdsSet (mem_singleton x))⟩

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_BilinearCoordinateMatrixPosDef
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
open Set Filter Matrix Manifold
open scoped Topology ContDiff
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma coordinateVector_self (p y : E) (i : CoordIndex E) :
    coordinateVector p y i = Module.finBasis ℝ E i := by
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (id : E → E) y (Module.finBasis ℝ E i) = _
  rw [mfderiv_id]
  rfl

lemma metricCoefficients_self (g : SmoothMetric E E) (p y : E) (i j : CoordIndex E) :
    metricCoefficients g p y i j = g.inner y (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) := by
  simp only [metricCoefficients,coordinateVector_self]
  rfl


end


open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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

lemma contDiffAt_metricFlux {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    ContDiffAt ℝ ∞ (fun z => metricFlux g u p z i) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  apply hd.mul
  apply ContDiffAt.sum
  intro j _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hv := (contDiffAt_inChart hu p hy).fderiv_right (m := ∞) (by simp)
  exact ha.mul (hv.clm_apply contDiffAt_const)

lemma contDiffAt_localLaplacian {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (localLaplacian g u p) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hn : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
    (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_metricFlux hu g p hy i).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma contMDiff_laplaceBeltrami {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (laplaceBeltrami g u) := by
  intro x
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  have hx := (chartAt E x).map_source (mem_chart_source E x)
  apply (contDiffAt_localLaplacian hu g x hx).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_target.mem_nhds hx] with y hy
  have he := laplaceBeltrami_inChart hu g x ((chartAt E x).symm y) ((chartAt E x).map_target hy)
  simpa only [Function.comp_apply, (chartAt E x).right_inv hy] using he

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
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

lemma roundPower_smooth (a b : Euclidean (d+1)) (k : ℕ) :
    ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ (roundPower a b k) := by
  have hc : ContDiff ℝ ∞ (fun x : Euclidean (d+1) => (planarLinear a b x)^k) :=
    (planarLinear a b).contDiff.pow k
  exact (Complex.reCLM.contDiff.comp hc).contMDiff.comp contMDiff_coe_sphere


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


theorem laplaceBeltrami_chart_metric (g : SmoothMetric E M) (ĝ : SmoothMetric E E)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) {u : M → ℝ} {f : E → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hg : ∀ᶠ z in 𝓝 y, ∀ v w : E, ĝ.inner z v w = g.inner ((chartAt E p).symm z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm z v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm z w))
    (hf : u ∘ (chartAt E p).symm =ᶠ[𝓝 y] f) :
    laplaceBeltrami g u ((chartAt E p).symm y) = laplaceBeltrami ĝ f y := by
  rw [laplaceBeltrami_inChart hu g p _ ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy]
  have ha : metricCoefficients ĝ y =ᶠ[𝓝 y] metricCoefficients g p := by
    filter_upwards [hg] with z hz
    ext i j
    rw [metricCoefficients_self]
    exact hz _ _
  have hflux : ∀ i, (fun z => metricFlux g u p z i) =ᶠ[𝓝 y]
      (fun z => metricFlux ĝ f y z i) := by
    intro i
    filter_upwards [ha, hf.fderiv (𝕜 := ℝ)] with z hz hdz
    simp only [metricFlux, hz, hdz, chartAt_self_eq, OpenPartialHomeomorph.refl_symm]
    rfl
  change localLaplacian g u p y = localLaplacian ĝ f y y
  simp only [localLaplacian, ← ha.eq_of_nhds]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [(hflux i).fderiv_eq]

theorem laplaceBeltrami_manifoldChartPush [T2Space M]
    (g : SmoothMetric E M) (ĝ : SmoothMetric E E) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ (chartAt E p).target)
    (hg : ∀ᶠ z in 𝓝 y, ∀ v w : E, ĝ.inner z v w = g.inner ((chartAt E p).symm z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm z v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm z w)) :
    laplaceBeltrami g (manifoldChartPush p f) ((chartAt E p).symm y) =
      laplaceBeltrami ĝ f y := by
  apply laplaceBeltrami_chart_metric g ĝ p hy (contMDiff_manifoldChartPush p hf hc hs) hg
  filter_upwards [(chartAt E p).open_target.mem_nhds hy] with z hz
  exact manifoldChartPush_apply p f hz

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactMetricInverseJets
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
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma geometric_complex_product_jet_bound
    {f g : E → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (h : ℕ) {F G R S : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*R^j)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*S^j) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ F*G*(R+S)^h := by
  calc
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (h-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*(F*R^i)*(G*S^(h-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfj i hi') (Nat.cast_nonneg _)
          (mul_nonneg hF (pow_nonneg hR _)))
        (hgj (h-i) (Nat.sub_le _ _))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg hG (pow_nonneg hS _))
    _ = F*G*(R+S)^h := by
      rw [add_pow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma compact_raw_jet_bound {O K : Set E} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) {f : E → F} (hf : ContDiffOn ℝ ∞ f O) (h : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ h, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hb (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    intro x hx
    exact (((hf.contDiffAt (hO.mem_nhds (hKO hx))).continuousAt_iteratedFDeriv
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))))).continuousWithinAt
  choose B hB using hb
  let C := 1+∑ j ∈ Finset.range (h+1), max 0 (B j)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  refine ⟨C,hC,?_⟩
  intro j hj x hx
  calc
    _ ≤ B j := hB j x hx
    _ ≤ max 0 (B j) := le_max_right _ _
    _ ≤ ∑ j ∈ Finset.range (h+1), max 0 (B j) :=
      Finset.single_le_sum (fun k _ => le_max_left _ _) (Finset.mem_range.mpr (by omega))
    _ ≤ C := by dsimp [C]; linarith
lemma complex_power_envelope_jet_bound {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : E) (h n : ℕ) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ A*(C)^j) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y^n) x‖ ≤ A^n*((n:ℝ)*C)^j := by
  induction n with
  | zero =>
    intro j hj
    cases j with
    | zero => simp only [pow_zero,norm_iteratedFDeriv_zero,norm_one,one_mul,le_refl]
    | succ j => simp only [pow_zero,iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,
        Nat.cast_zero,zero_mul,zero_pow (by omega : j+1 ≠ 0),mul_zero,le_refl]
  | succ n ih =>
    intro j hj
    have hb := geometric_complex_product_jet_bound (hf.pow n) hf x j
      (pow_nonneg hA _) hA (mul_nonneg (Nat.cast_nonneg _) hC) hC
      (fun k hk => ih k (hk.trans hj)) (fun k hk => hfj k (hk.trans hj))
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hb


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
open Set Filter Function Manifold BoxIntegral Metric
open scoped Topology ContDiff

lemma sphericalRadius_eq_planar_norm (a b : Euclidean 4) (q : Sphere 3) :
    sphericalRadius a b q = ‖planarLinear a b q‖ := by
  have hh := Complex.sq_norm (planarLinear a b q)
  simp only [planarLinear_apply,Complex.normSq_apply,Complex.add_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,
    zero_mul,sub_zero,add_zero,Complex.add_im,Complex.mul_im,zero_add] at hh
  have hs := sphericalRadius_sq a b q
  apply (sq_eq_sq₀ (sphericalRadius_nonneg a b q) (norm_nonneg _)).mp
  rw [hs]
  change _ = ‖(⟪a,(q : Euclidean 4)⟫_ℝ : ℂ)+Complex.I*⟪b,(q : Euclidean 4)⟫_ℝ‖^2
  nlinarith only [hh]

lemma spherical_chart_pullback_smooth {φ : Sphere 3 → ℝ}
    (hφ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ) (p : Sphere 3) :
    ContDiff ℝ ∞ (φ ∘ (chartAt (Euclidean 3) p).symm) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  exact contDiffAt_inChart hφ p (by rw [sphere_chart_target]; trivial)


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
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartJetBoundGlobalValue
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
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Function
open scoped Topology ContDiff Manifold
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma contDiffOn_chartTransition_for_jets (p q : M) :
    ContDiffOn ℝ ∞ ((chartAt E p).symm.trans (chartAt E q))
      ((chartAt E p).symm.trans (chartAt E q)).source := by
  intro y hy
  have hy' : y ∈ (chartAt E p).target ∧ (chartAt E p).symm y ∈ (chartAt E q).source := hy
  exact (contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hy'.2).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy'.1))).contDiffWithinAt

theorem compact_chart_jet_transfer (p q : M) {L : Set M} (hL : IsCompact L)
    (hLp : L ⊆ (chartAt E p).source) {K : Set E} (hK : IsCompact K)
    (hKq : K ⊆ (chartAt E q).target) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : M → F) (f : E → F), ContDiff ℝ ∞ f →
      tsupport U ⊆ L → (∀ z ∈ (chartAt E p).target, U ((chartAt E p).symm z)=f z) →
      ∀ y ∈ K, ∀ j ≤ m, ∀ B : ℝ, 0 ≤ B →
        (∀ i ≤ j, ‖iteratedFDeriv ℝ i f (chartAt E p ((chartAt E q).symm y))‖ ≤ B) →
        ‖iteratedFDeriv ℝ j (U ∘ (chartAt E q).symm) y‖ ≤ C*B := by
  let c := chartAt E p
  let d := chartAt E q
  let T := (d.symm '' K) ∩ L
  have hT : IsCompact T := (hK.image_of_continuousOn (d.continuousOn_symm.mono hKq)).inter_right hL.isClosed
  have hTd : T ⊆ d.source := by
    rintro x ⟨⟨y,hy,rfl⟩,_⟩
    exact d.map_target (hKq hy)
  let S := d '' T
  have hS : IsCompact S := hT.image_of_continuousOn (d.continuousOn.mono hTd)
  let e := d.symm.trans c
  have hSe : S ⊆ e.source := by
    rintro y ⟨x,hx,rfl⟩
    refine ⟨d.map_source (hTd hx),?_⟩
    change d.symm (d x) ∈ c.source
    rw [d.left_inv (hTd hx)]
    exact hLp hx.2
  obtain ⟨ψ,hψ,heψ⟩ := smooth_extension_near_compact hS e.open_source hSe
    (contDiffOn_chartTransition_for_jets q p)
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound isOpen_univ hK (subset_univ _)
    hψ.contDiffOn m
  let C : ℝ := (m.factorial : ℝ)*D^m+1
  have hCp : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hCp,?_⟩
  intro U f hf hUs hUf y hy j hj B hB hfj
  by_cases hx : d.symm y ∈ L
  · have hyS : y ∈ S := ⟨d.symm y,⟨⟨y,hy,rfl⟩,hx⟩,d.right_inv (hKq hy)⟩
    have hey := hSe hyS
    have heψy : (e : E → E) =ᶠ[𝓝 y] ψ := heψ.filter_mono (nhds_le_nhdsSet hyS)
    have heq : U ∘ d.symm =ᶠ[𝓝 y] f ∘ ψ := by
      filter_upwards [e.open_source.mem_nhds hey,heψy] with z hz hzz
      have hcz : d.symm z ∈ c.source := hz.2
      change U (d.symm z)=f (ψ z)
      rw [←hzz]
      change U (d.symm z)=f (c (d.symm z))
      rw [←hUf _ (c.map_source hcz),c.left_inv hcz]
    rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
    have hb : ∀ i ≤ j, ‖iteratedFDeriv ℝ i f (ψ y)‖ ≤ B := by
      intro i hi
      rw [←heψy.eq_of_nhds]
      exact hfj i hi
    have hd : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i ψ y‖ ≤ D^i := by
      intro i hi hij
      exact (hDj i (hij.trans hj) y hy).trans (by simpa using pow_le_pow_right₀ hD hi)
    have hbound := norm_iteratedFDeriv_comp_le hf hψ
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))) y hb hd
    apply hbound.trans
    have hfact : (j.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hj
    have hp := pow_le_pow_right₀ hD hj
    have hmul := mul_le_mul hfact hp (pow_nonneg (zero_le_one.trans hD) _) (Nat.cast_nonneg _)
    calc
      _ = ((j.factorial : ℝ)*D^j)*B := by ring
      _ ≤ ((m.factorial : ℝ)*D^m)*B := mul_le_mul_of_nonneg_right hmul hB
      _ ≤ C*B := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hB
  · have hn : d.symm y ∉ tsupport U := fun h => hx (hUs h)
    have he : U ∘ d.symm =ᶠ[𝓝 y] (fun _ => (0:F)) :=
      (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto (d.continuousAt_symm (hKq hy)).tendsto
    rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
    simpa using mul_nonneg hCp.le hB


end

open Set Filter Function Manifold
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_RoundPowerWeightedChartJets
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
section EnvelopePowers
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma real_power_envelope_jet_bound_on [FiniteDimensional ℝ E]
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f O) (h n : ℕ) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ A*(C)^j) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (f y^n).re) x‖ ≤ A^n*((n:ℝ)*C)^j := by
  obtain ⟨F,hF,he⟩ := smooth_extension_at hO hxO hf
  have hh := complex_power_envelope_jet_bound hF x h n hA hC (fun j hj => by
    rw [←(he.iteratedFDeriv ℝ j).self_of_nhds]
    exact hfj j hj)
  intro j hj
  have heRe : (fun y => (f y^n).re) =ᶠ[𝓝 x] (fun y => (F y^n).re) :=
    he.mono (fun y hy => congrArg (fun z : ℂ => (z^n).re) hy)
  rw [(heRe.iteratedFDeriv ℝ j).self_of_nhds]
  calc
    _ ≤ ‖Complex.reCLM‖*‖iteratedFDeriv ℝ j (fun y => F y^n) x‖ :=
      ContinuousLinearMap.norm_iteratedFDeriv_comp_left Complex.reCLM (x:=x)
        (hF.pow n).contDiffAt (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
    _ ≤ 1*(A^n*((n:ℝ)*C)^j) := mul_le_mul (le_of_eq Complex.reCLM_norm)
      (hh j hj) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _
end EnvelopePowers


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
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
variable {d : ℕ}

theorem roundPower_weighted_chart_jets
    (a b : Euclidean (d+1)) (p : Sphere d) {K : Set (Euclidean d)}
    (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean d) p).target)
    (φ : Euclidean d → ℝ) (hφ : ContinuousOn φ K) (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) y‖ ≤
        C*(n:ℝ)^j*(Real.exp ((n:ℝ)*φ y)+‖roundPlanarChart a b p y‖^n) := by
  have hf := roundPlanarChart_smooth a b p
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound (chartAt (Euclidean d) p).open_target hK hKO hf h
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hφ
  let r := Real.exp (-B)
  have hr : 0 < r := Real.exp_pos _
  let T := max 1 (D/r)
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  refine ⟨T^h,pow_pos (zero_lt_one.trans_le hT1) _,?_⟩
  intro n y hy j hj
  let A := max ‖roundPlanarChart a b p y‖ (Real.exp (φ y))
  have hA : 0 ≤ A := (norm_nonneg _).trans (le_max_left _ _)
  have hrA : r ≤ A := by
    have hlow : -B ≤ φ y := by
      have hh := (neg_abs_le (φ y)).trans' (neg_le_neg (hB y hy))
      simpa only [Real.norm_eq_abs] using hh
    exact (Real.exp_le_exp.mpr hlow).trans (le_max_right _ _)
  have hraw : ∀ k ≤ h, ‖iteratedFDeriv ℝ k (roundPlanarChart a b p) y‖ ≤ A*T^k := by
    intro k hk
    by_cases hk0 : k=0
    · subst k
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using (le_max_left
        ‖roundPlanarChart a b p y‖ (Real.exp (φ y)))
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hTk : T ≤ T^k := by simpa only [pow_one] using pow_le_pow_right₀ hT1 hk1
      calc
        _ ≤ D := hDj k hk y hy
        _ = r*(D/r) := by field_simp
        _ ≤ A*T^k := mul_le_mul hrA ((le_max_right _ _).trans hTk)
          (div_nonneg (zero_le_one.trans hD) hr.le) hA
  have hp := real_power_envelope_jet_bound_on (chartAt (Euclidean d) p).open_target
    (hKO hy) hf h n hA hT0 hraw j hj
  have hAn : A^n ≤ Real.exp ((n:ℝ)*φ y)+‖roundPlanarChart a b p y‖^n := by
    by_cases he : ‖roundPlanarChart a b p y‖ ≤ Real.exp (φ y)
    · dsimp [A]
      rw [max_eq_right he,←Real.exp_nat_mul]
      exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
    · dsimp [A]
      rw [max_eq_left (le_of_not_ge he)]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have he : A^n*((n:ℝ)*T)^j = T^j*(n:ℝ)^j*A^n := by rw [mul_pow]; ring
  rw [he] at hp
  exact hp.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT1 hj) (pow_nonneg (Nat.cast_nonneg _) _))
    hAn (pow_nonneg hA _) (by positivity))


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_TransverseZeroKernel
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
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma laplaceBeltrami_add {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun y => u y + v y) x =
      laplaceBeltrami g u x + laplaceBeltrami g v x := by
  have h := congrArg Complex.re (complexLaplaceBeltrami_add
    (Complex.ofRealCLM.contMDiff.comp hu) (Complex.ofRealCLM.contMDiff.comp hv) g x)
  simpa only [complexLaplaceBeltrami, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
    Function.comp_def, Complex.ofRealCLM_apply, Pi.sub_apply] using h

end

open Set Filter Function Manifold
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_PinningFactorGradient
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma laplaceBeltrami_congr_nhds (g : SmoothMetric E M) {u v : M → ℝ} {x : M}
    (hu : u =ᶠ[𝓝 x] v) : laplaceBeltrami g u x=laplaceBeltrami g v x := by
  let c := chartAt E x
  have hx := c.map_source (mem_chart_source E x)
  have ht : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv (mem_chart_source E x)] using (c.continuousAt_symm hx).tendsto
  have hu' := (hu.comp_tendsto ht).fderiv (𝕜:=ℝ)
  have he (i : CoordIndex E) :
      (fun y => Real.sqrt (metricCoefficients g x y).det * ∑ j,
        (metricCoefficients g x y)⁻¹ i j * fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))
      =ᶠ[𝓝 (c x)]
      (fun y => Real.sqrt (metricCoefficients g x y).det * ∑ j,
        (metricCoefficients g x y)⁻¹ i j * fderiv ℝ (v ∘ c.symm) y (Module.finBasis ℝ E j)) := by
    filter_upwards [hu'] with y hy
    rw [hy]
  unfold laplaceBeltrami
  change (Real.sqrt (metricCoefficients g x (c x)).det)⁻¹ * ∑ i, _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun T : E →L[ℝ] ℝ => T (Module.finBasis ℝ E i)) (he i).fderiv_eq

lemma laplaceBeltrami_tsupport (g : SmoothMetric E M) (u : M → ℝ) :
    tsupport (laplaceBeltrami g u) ⊆ tsupport u := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have he := laplaceBeltrami_congr_nhds g (notMem_tsupport_iff_eventuallyEq.mp hn)
  have hz : laplaceBeltrami g (fun _ : M => (0:ℝ)) x=0 := by
    simp [laplaceBeltrami,Function.comp_def]
  exact hx (he.trans hz)

lemma laplaceResidual_tsupport (g : SmoothMetric E M) (u : M → ℝ) (Λ : ℝ) :
    tsupport (fun x => laplaceBeltrami g u x+Λ*u x) ⊆ tsupport u := by
  apply (tsupport_add _ _).trans
  apply union_subset (laplaceBeltrami_tsupport g u)
  exact tsupport_mul_subset_right (f := fun _ : M => Λ) (g := u)

variable [T2Space M]

theorem compact_chart_weighted_jet_transfer (p q : M) {L : Set M} (hL : IsCompact L)
    (hLp : L ⊆ (chartAt E p).source) {K : Set E} (hK : IsCompact K)
    (hKq : K ⊆ (chartAt E q).target) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : M → ℝ) (f : E → ℝ), ContDiff ℝ ∞ f →
      tsupport U ⊆ L → (∀ z ∈ (chartAt E p).target, U ((chartAt E p).symm z)=f z) →
      ∀ (B : ℕ → M → ℝ), (∀ j x, 0 ≤ B j x) →
      (∀ x ∈ L, ∀ j ≤ m, ∀ i ≤ j,
        ‖iteratedFDeriv ℝ i f (chartAt E p x)‖ ≤ B j x) →
      ∀ y ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (U ∘ (chartAt E q).symm) y‖ ≤ C*B j ((chartAt E q).symm y) := by
  obtain ⟨C,hC,hT⟩ := compact_chart_jet_transfer (F := ℝ) p q hL hLp hK hKq m
  refine ⟨C,hC,?_⟩
  intro U f hf hs he B hB hb y hy j hj
  by_cases hx : (chartAt E q).symm y ∈ L
  · exact hT U f hf hs he y hy j hj _ (hB j _) (fun i hi => hb _ hx j hj i hi)
  · have hn : (chartAt E q).symm y ∉ tsupport U := fun h => hx (hs h)
    have hzero : U ∘ (chartAt E q).symm =ᶠ[𝓝 y] (fun _ => (0:ℝ)) :=
      (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
        ((chartAt E q).continuousAt_symm (hKq hy)).tendsto
    rw [(hzero.iteratedFDeriv ℝ j).eq_of_nhds]
    simpa using mul_nonneg hC.le (hB j ((chartAt E q).symm y))


end



open Set Filter Function Manifold Metric
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeCoupledCleanChartJets
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
open Set Filter Manifold
open scoped Topology ContDiff

lemma sphericalWaveLift_apply (u : Euclidean 3 → ℝ) (y : Euclidean 3) :
    sphericalWaveLift u ((chartAt (Euclidean 3) sourcePole).symm y)=u y :=
  manifoldChartPush_apply sourcePole u (by rw [sphere_chart_target]; trivial)

lemma sphericalWaveLift_smooth {u : Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ (sphericalWaveLift u) :=
  contMDiff_manifoldChartPush sourcePole hu hc (by rw [sphere_chart_target]; exact subset_univ _)

lemma sphericalWaveLift_tsupport {u : Euclidean 3 → ℝ} (hc : HasCompactSupport u)
    {r : ℝ} (hs : tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < r}) :
    tsupport (sphericalWaveLift u) ⊆ {q | sphericalRadius sourceAxisOne sourceAxisTwo q < r} := by
  intro q hq
  obtain ⟨y,hy,rfl⟩ := manifoldChartPush_tsupport sourcePole hc
    (by rw [sphere_chart_target]; exact subset_univ _) hq
  exact hs hy

lemma sphericalWaveLift_laplacian (g : SmoothMetric (Euclidean 3) (Sphere 3))
    {u : Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (y : Euclidean 3) :
    laplaceBeltrami g (sphericalWaveLift u) ((chartAt (Euclidean 3) sourcePole).symm y)=
      laplaceBeltrami (sphereChartMetric g sourcePole) u y := by
  apply laplaceBeltrami_manifoldChartPush g (sphereChartMetric g sourcePole) sourcePole
    (by rw [sphere_chart_target]; trivial) hu hc (by rw [sphere_chart_target]; exact subset_univ _)
  exact Filter.Eventually.of_forall (fun z v w => chartMetricForm_pairing g sourcePole z v w)

lemma spherical_sublevel_compact (r : ℝ) :
    IsCompact {q : Sphere 3 | sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r} :=
  (isClosed_le (sphericalRadius_continuous _ _) continuous_const).isCompact

theorem spherical_wave_lift_jets (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (p : Sphere 3) {K : Set (Euclidean 3)} (hK : IsCompact K) {r : ℝ} (hr : r < 1)
    (m : ℕ) : ∃ C > 0, ∀ (u : Euclidean 3 → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
        ((chartAt (Euclidean 3) sourcePole).symm y) < r} →
      ∀ (B : ℕ → Sphere 3 → ℝ), (∀ j q, 0 ≤ B j q) →
      ∀ (R : Sphere 3 → ℝ), (∀ q, 0 ≤ R q) → ∀ Λ : ℝ,
      (∀ x : Euclidean 3, ∀ j ≤ m, ∀ i ≤ j,
        ‖iteratedFDeriv ℝ i u x‖ ≤ B j ((chartAt (Euclidean 3) sourcePole).symm x)) →
      (∀ x : Euclidean 3, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (sphereChartMetric g sourcePole) u y+Λ*u y) x‖ ≤
          R ((chartAt (Euclidean 3) sourcePole).symm x)) →
      ∀ y ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (sphericalWaveLift u ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤
          C*B j ((chartAt (Euclidean 3) p).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g (sphericalWaveLift u) q+Λ*sphericalWaveLift u q) ∘
          (chartAt (Euclidean 3) p).symm) y‖ ≤ C*R ((chartAt (Euclidean 3) p).symm y) := by
  let L : Set (Sphere 3) := {q | sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r}
  have hLp : L ⊆ (chartAt (Euclidean 3) sourcePole).source :=
    sphericalRadius_sublevel_in_source sourcePole _ _ sphericalRadius_neg_sourcePole hr
  obtain ⟨C,hC,htransfer⟩ := compact_chart_weighted_jet_transfer sourcePole p
    (spherical_sublevel_compact r) hLp hK (by rw [sphere_chart_target]; exact subset_univ _) m
  refine ⟨C,hC,?_⟩
  intro u hu hc hs B hB R hR Λ hj hres y hy j h_j
  have hUs : tsupport (sphericalWaveLift u) ⊆ L := by
    intro q hq
    exact (show sphericalRadius sourceAxisOne sourceAxisTwo q < r from
      sphericalWaveLift_tsupport hc hs hq).le
  have he : ∀ z ∈ (chartAt (Euclidean 3) sourcePole).target,
      sphericalWaveLift u ((chartAt (Euclidean 3) sourcePole).symm z)=u z :=
    fun z _ => sphericalWaveLift_apply u z
  have hUsm := sphericalWaveLift_smooth hu hc
  have hRs : tsupport (fun q => laplaceBeltrami g (sphericalWaveLift u) q+Λ*sphericalWaveLift u q) ⊆ L :=
    (laplaceResidual_tsupport g _ Λ).trans hUs
  have hRsm : ContDiff ℝ ∞ (fun y => laplaceBeltrami (sphereChartMetric g sourcePole) u y+Λ*u y) := by
    rw [←contMDiff_iff_contDiff]
    exact (contMDiff_laplaceBeltrami (contMDiff_iff_contDiff.mpr hu) _).add
      (contMDiff_const.mul (contMDiff_iff_contDiff.mpr hu))
  constructor
  · apply htransfer _ u hu hUs he B hB _ y hy j h_j
    intro q hq j hjm i hij
    simpa only [(chartAt (Euclidean 3) sourcePole).left_inv (hLp hq)] using
      hj (chartAt (Euclidean 3) sourcePole q) j hjm i hij
  · apply htransfer _ _ hRsm hRs _ (fun _ => R) (fun _ => hR) _ y hy j h_j
    · intro z _
      simp only [sphericalWaveLift_laplacian g hu hc,sphericalWaveLift_apply]
    · intro q hq j hjm i hij
      simpa only [(chartAt (Euclidean 3) sourcePole).left_inv (hLp hq)] using
        hres (chartAt (Euclidean 3) sourcePole q) i (hij.trans hjm)


end


section
open Set Filter Manifold
open scoped Topology ContDiff

lemma sphericalWeight_pos (φ : Sphere 3 → ℝ) (n : ℕ) (q : Sphere 3) :
    0 < sphericalWeight φ n q := add_pos_of_pos_of_nonneg (Real.exp_pos _) (by positivity)

end


section
open Set Filter Manifold
open scoped Topology ContDiff InnerProductSpace

lemma sphericalWeight_chart (φ : Sphere 3 → ℝ) (p : Sphere 3) (n : ℕ) (y : Euclidean 3) :
    sphericalWeight φ n ((chartAt (Euclidean 3) p).symm y) =
      Real.exp ((n:ℝ)*(φ ∘ (chartAt (Euclidean 3) p).symm) y)+
        ‖roundPlanarChart sourceAxisOne sourceAxisTwo p y‖^n := rfl

lemma sphericalWeight_ge_exp (φ : Sphere 3 → ℝ) (n : ℕ) (q : Sphere 3) :
    Real.exp ((n:ℝ)*φ q) ≤ sphericalWeight φ n q :=
  le_add_of_nonneg_right (by positivity)

lemma real_smooth_add_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f h : E → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (f+h) x‖ ≤ ‖iteratedFDeriv ℝ j f x‖+‖iteratedFDeriv ℝ j h x‖ := by
  have hj : (j : WithTop ℕ∞) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  rw [iteratedFDeriv_add_apply (hf.of_le hj).contDiffAt (hh.of_le hj).contDiffAt]
  exact norm_add_le _ _

theorem spherical_wave_background_chart_bounds_oai
    (g g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {F : Set (Sphere 3)} (hF : IsClosed F)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    {φ : Sphere 3 → ℝ} (hφ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ)
    (hgap : ∀ q ∈ F, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
      Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q)
    (p : Sphere 3) {K : Set (Euclidean 3)} (hK : IsCompact K)
    {r : ℝ} (hr : r < 1) (m D : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
    ∀ (u : Euclidean 3 → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
        ((chartAt (Euclidean 3) sourcePole).symm y) < r} →
      (∀ y : Euclidean 3, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(n:ℝ)^(j+4)*
          Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm y)) ∧
        ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (sphereChartMetric g sourcePole) u y+
          sphereFrequency n*u y) y‖ ≤ C₀*((n:ℝ)^(D+1))⁻¹*
          Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm y))) →
      ∀ y ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j ((roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) ∘
          (chartAt (Euclidean 3) p).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*sphericalWeight φ n ((chartAt (Euclidean 3) p).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
          (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
          sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q) ∘
          (chartAt (Euclidean 3) p).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*sphericalWeight φ n ((chartAt (Euclidean 3) p).symm y) := by
  have hKt : K ⊆ (chartAt (Euclidean 3) p).target := by rw [sphere_chart_target]; exact subset_univ _
  obtain ⟨C₁,hC₁,hback⟩ := roundPower_weighted_chart_jets sourceAxisOne sourceAxisTwo p hK hKt
    (φ ∘ (chartAt (Euclidean 3) p).symm) (hφ.continuous.comp (sphere_chart_symm_continuous p)).continuousOn m
  obtain ⟨N,hN,hres⟩ := roundPower_global_profile_residual_rapid_decay g g₀ hg₀ hF hext
    sourceAxisOne sourceAxisTwo source_axes_orthonormal.1 source_axes_orthonormal.2.1
    source_axes_orthonormal.2.2 p hK hKt (φ ∘ (chartAt (Euclidean 3) p).symm)
    (hφ.continuous.comp (sphere_chart_symm_continuous p)).continuousOn m D
    (fun y _ hy hz => by
      have h := hgap _ hy (by
        rw [sphericalRadius_eq_planar_norm]
        exact norm_pos_iff.mpr hz)
      simpa only [sphericalRadius_eq_planar_norm,roundPlanarChart,Function.comp_apply] using h)
  obtain ⟨T,hT,htransfer⟩ := spherical_wave_lift_jets g p hK hr m
  let C := C₁+1+T*C₀
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast ((le_max_right N 1).trans hn)
  have hn0 : (0:ℝ)<n := zero_lt_one.trans_le hn1
  have hnD : 0 < (n:ℝ)^D := pow_pos hn0 _
  have hn4 : (1:ℝ)≤(n:ℝ)^4 := one_le_pow₀ hn1
  intro u hu hc hs hj y hy j hjm
  let W := sphericalWeight φ n ((chartAt (Euclidean 3) p).symm y)
  have hW : 0 < W := sphericalWeight_pos φ n _
  have hE := sphericalWeight_ge_exp φ n ((chartAt (Euclidean 3) p).symm y)
  let B := fun j q => C₀*(n:ℝ)^(j+4)*Real.exp ((n:ℝ)*φ q)
  let R := fun q => C₀*((n:ℝ)^(D+1))⁻¹*Real.exp ((n:ℝ)*φ q)
  have hlift := htransfer u hu hc hs B (fun j q => by dsimp [B]; positivity)
    R (fun q => by dsimp [R]; positivity) (sphereFrequency n)
    (fun x j hjm i hij => (hj x i (hij.trans hjm)).1.trans (by
      dsimp [B]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by omega : i+4≤j+4)) hC₀.le)
        (Real.exp_pos _).le))
    (fun x j hjm => (hj x j hjm).2) y hy j hjm
  have hback' := hback n y hy j hjm
  rw [←sphericalWeight_chart] at hback'
  have hres' := hres n ((le_max_left _ _).trans hn) y hy j hjm
  have hsmooth := sphericalWaveLift_smooth hu hc
  have hsum : ((roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) ∘
      (chartAt (Euclidean 3) p).symm)=
      (roundPower sourceAxisOne sourceAxisTwo n ∘ (chartAt (Euclidean 3) p).symm)+
      (sphericalWaveLift u ∘ (chartAt (Euclidean 3) p).symm) := rfl
  have hroundsm := roundPower_smooth sourceAxisOne sourceAxisTwo n
  constructor
  · rw [hsum]
    apply (real_smooth_add_jet_bound (spherical_chart_pullback_smooth hroundsm p)
      (spherical_chart_pullback_smooth hsmooth p) j y).trans
    apply (add_le_add hback' hlift.1).trans
    have hnj : (n:ℝ)^j ≤ (n:ℝ)^(j+4) := pow_le_pow_right₀ hn1 (by omega)
    calc
      _ ≤ C₁*(n:ℝ)^(j+4)*W+T*(C₀*(n:ℝ)^(j+4)*W) :=
        add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnj hC₁.le) hW.le)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (by positivity)) hT.le)
      _ ≤ C*(n:ℝ)^(j+4)*W := by dsimp [C]; nlinarith [mul_nonneg (pow_nonneg hn0.le (j+4)) hW.le]
  · let R₁ := fun q => laplaceBeltrami g (roundPower sourceAxisOne sourceAxisTwo n) q+
      sphereFrequency n*roundPower sourceAxisOne sourceAxisTwo n q
    let R₂ := fun q => laplaceBeltrami g (sphericalWaveLift u) q+
      sphereFrequency n*sphericalWaveLift u q
    have hR₁ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ R₁ :=
      (contMDiff_laplaceBeltrami hroundsm g).add (contMDiff_const.mul hroundsm)
    have hR₂ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ R₂ :=
      (contMDiff_laplaceBeltrami hsmooth g).add (contMDiff_const.mul hsmooth)
    have he : ((fun q => laplaceBeltrami g
        (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
        sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q) ∘
        (chartAt (Euclidean 3) p).symm)=
        (R₁ ∘ (chartAt (Euclidean 3) p).symm)+(R₂ ∘ (chartAt (Euclidean 3) p).symm) := by
      funext x
      have h2 : (2 : WithTop ℕ∞) ≤ ∞ :=
        le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
      have hadd := laplaceBeltrami_add (hroundsm.of_le h2) (hsmooth.of_le h2) g
        ((chartAt (Euclidean 3) p).symm x)
      dsimp only [Function.comp_apply,Pi.add_apply,R₁,R₂]
      change laplaceBeltrami g (fun y => roundPower sourceAxisOne sourceAxisTwo n y+sphericalWaveLift u y)
        ((chartAt (Euclidean 3) p).symm x) + _ = _
      rw [hadd]
      ring
    rw [he]
    apply (real_smooth_add_jet_bound (spherical_chart_pullback_smooth hR₁ p)
      (spherical_chart_pullback_smooth hR₂ p) j y).trans
    apply (add_le_add hres' hlift.2).trans
    have hinv : ((n:ℝ)^(D+1))⁻¹ ≤ ((n:ℝ)^D)⁻¹ :=
      inv_anti₀ hnD (pow_le_pow_right₀ hn1 (by omega))
    calc
      _ ≤ ((n:ℝ)^D)⁻¹*W+T*(C₀*((n:ℝ)^D)⁻¹*W) :=
        add_le_add (mul_le_mul_of_nonneg_left hE (by positivity))
          (mul_le_mul_of_nonneg_left (mul_le_mul
            (mul_le_mul_of_nonneg_left hinv hC₀.le) hE
            (Real.exp_pos _).le (by positivity)) hT.le)
      _ = (1+T*C₀)/(n:ℝ)^D*W := by rw [div_eq_mul_inv]; ring
      _ ≤ C*(n:ℝ)^4/(n:ℝ)^D*W := by
        apply mul_le_mul_of_nonneg_right _ hW.le
        apply div_le_div_of_nonneg_right _ hnD.le
        calc
          1+T*C₀ ≤ C := by dsimp [C]; linarith
          _ ≤ C*(n:ℝ)^4 := le_mul_of_one_le_right (by dsimp [C]; positivity) hn4

end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.spherical_wave_background_chart_bounds_oai := @OAI.YauCounterexamples.spherical_wave_background_chart_bounds_oai
