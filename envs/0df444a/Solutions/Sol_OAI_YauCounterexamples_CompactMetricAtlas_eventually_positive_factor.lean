-- Prove2me | solution 1 for OAI.YauCounterexamples.CompactMetricAtlas.eventually_positive_factor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:52:42.444653+00:00
-- url     : https://prove2.me/submissions/8ee48c34-bb99-460f-a571-aed1f09d5351

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_AnisotropicCompositionSmall
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
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
section Neumann
variable {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

lemma neumannCorrectedInverse_bound (R : Y →L[𝕜] X) (P : X →L[𝕜] Y)
    (h : ‖R ∘L P‖ < 1) (C : ℝ) (hR : ‖R‖ ≤ C) (hq : C * ‖P‖ ≤ 1 / 2) (f : Y) :
    ‖neumannCorrectedInverse R P h f‖ ≤ 2 * C * ‖f‖ := by
  have hC := (norm_nonneg R).trans hR
  let u := neumannCorrectedInverse R P h f
  have hu : ‖u‖ ≤ C * (‖f‖ + ‖P‖ * ‖u‖) := by
    conv_lhs => rw [show u = R (f + P u) from neumannCorrectedInverse_fixed R P h f]
    exact (R.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hR (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
        (add_le_add le_rfl (P.le_opNorm u))) hC))
  have hp := mul_le_mul_of_nonneg_right hq (norm_nonneg u)
  dsimp only [u] at hu hp
  nlinarith

end Neumann

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ConformalMetric
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma conformalMetric_coefficients (g : SmoothMetric E M) (b : M → ℝ)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b) (hpos : ∀ x, 0 < b x) (p : M) (y : E) :
    metricCoefficients (conformalMetric g b hb hpos) p y =
      (b ((chartAt E p).symm y)) ^ 2 • metricCoefficients g p y := rfl

lemma real_matrix_inv_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Matrix ι ι ℝ) {c : ℝ} (hc : c ≠ 0) : (c • a)⁻¹ = c⁻¹ • a⁻¹ := by
  by_cases ha : IsUnit a.det
  · let : Invertible c := invertibleOfNonzero hc
    rw [Matrix.inv_smul a c ha, invOf_eq_inv]
  · have hz : a.det = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using ha
    have hz' : ¬IsUnit (c • a).det := by simp [hz]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ ha, Matrix.nonsing_inv_apply_not_isUnit _ hz', smul_zero]

lemma conformalMetric_inverse (g : SmoothMetric E M) (b : M → ℝ)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b) (hpos : ∀ x, 0 < b x) (p : M) (y : E) :
    (metricCoefficients (conformalMetric g b hb hpos) p y)⁻¹ =
      ((b ((chartAt E p).symm y)) ^ 2)⁻¹ • (metricCoefficients g p y)⁻¹ := by
  rw [conformalMetric_coefficients, real_matrix_inv_smul _ (pow_ne_zero 2 (ne_of_gt (hpos _)))]

lemma conformalMetric_density_three (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E M) (b : M → ℝ)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b) (hpos : ∀ x, 0 < b x) (p : M) (y : E) :
    Real.sqrt (Matrix.det (metricCoefficients (conformalMetric g b hb hpos) p y)) =
      (b ((chartAt E p).symm y)) ^ 3 * Real.sqrt (Matrix.det (metricCoefficients g p y)) := by
  rw [conformalMetric_coefficients, Matrix.det_smul]
  simp only [Fintype.card_fin, CoordIndex, hd]
  rw [show ((b ((chartAt E p).symm y)) ^ 2) ^ 3 = ((b ((chartAt E p).symm y)) ^ 3) ^ 2 by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (hpos _).le _)]

lemma conformalMetric_laplacian_three (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E M) (b : M → ℝ)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b) (hpos : ∀ x, 0 < b x) (u : M → ℝ) (x : M) :
    laplaceBeltrami (conformalMetric g b hb hpos) u x =
      (b x ^ 3)⁻¹ * weightedLaplacian g b u x := by
  let c := chartAt E x
  have hx : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hflux : ∀ i, (fun y => Real.sqrt (Matrix.det (metricCoefficients (conformalMetric g b hb hpos) x y)) *
      ∑ j, (metricCoefficients (conformalMetric g b hb hpos) x y)⁻¹ i j *
        fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j)) =
      (fun y => b (c.symm y) * (Real.sqrt (Matrix.det (metricCoefficients g x y)) *
      ∑ j, (metricCoefficients g x y)⁻¹ i j * fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))) := by
    intro i
    funext y
    rw [conformalMetric_density_three hd, conformalMetric_inverse]
    simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    have hn := ne_of_gt (hpos (c.symm y))
    dsimp only [c] at hn ⊢
    field_simp [hn]
  dsimp only [c] at hflux hx
  unfold laplaceBeltrami weightedLaplacian
  dsimp only
  simp only [hflux]
  rw [conformalMetric_density_three hd, hx, mul_inv_rev]
  ring

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

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
section ProductCalculus
variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [RCLike 𝕜]
lemma second_fderiv_mul_at {u v : E → 𝕜} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => u z * v z) y b) x a =
      u x * fderiv ℝ (fun y => fderiv ℝ v y b) x a +
      v x * fderiv ℝ (fun y => fderiv ℝ u y b) x a +
      fderiv ℝ u x a * fderiv ℝ v x b +
      fderiv ℝ u x b * fderiv ℝ v x a := by
  have hdu := hu.differentiableAt (by norm_num)
  have hdv := hv.differentiableAt (by norm_num)
  have hdu' : DifferentiableAt ℝ (fun y => fderiv ℝ u y b) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have hdv' : DifferentiableAt ℝ (fun y => fderiv ℝ v y b) x :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have he : (fun y => fderiv ℝ (fun z => u z * v z) y b) =ᶠ[𝓝 x]
      (fun y => u y * fderiv ℝ v y b + v y * fderiv ℝ u y b) := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y hy hz
    rw [fderiv_fun_mul (hy.differentiableAt (by norm_num)) (hz.differentiableAt (by norm_num))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [he.fderiv_eq]
  erw [fderiv_fun_add (hdu.mul hdv') (hdv.mul hdu'),
    fderiv_fun_mul hdu hdv', fderiv_fun_mul hdv hdu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring
end ProductCalculus
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma laplaceBeltrami_mul {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun y => u y * v y) x =
      u x * laplaceBeltrami g v x + v x * laplaceBeltrami g u x +
        2 * coordinateGradientPair g u v x := by
  let c := chartAt E x
  let b := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hv' := contDiffAt_inChart_C2 hv x hx
  change localLaplacian g _ x (c x) = _
  have huv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (fun y => u y * v y) := hu.mul hv
  rw [localLaplacian_expansion_C2 huv g x hx]
  change _ = u x * localLaplacian g v x (c x) +
    v x * localLaplacian g u x (c x) + 2 * coordinateGradientPair g u v x
  rw [localLaplacian_expansion_C2 hu g x hx, localLaplacian_expansion_C2 hv g x hx]
  have hs (i j : CoordIndex E) : (metricCoefficients g x (c x))⁻¹ j i =
      (metricCoefficients g x (c x))⁻¹ i j := by
    have h := congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A i j)
      (metricCoefficients_posDef g x hx).inv.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hcross : (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) (c x) (b j) * fderiv ℝ (v ∘ c.symm) (c x) (b i)) =
      coordinateGradientPair g u v x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs]
  change (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (fun y => fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) y (b j)) (c x) (b i)) +
      ∑ j, metricFirstCoefficient g x j (c x) *
        fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) (c x) (b j) = _
  have hd1 (j : CoordIndex E) :
      fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) (c x) (b j) =
        u x * fderiv ℝ (v ∘ c.symm) (c x) (b j) +
        v x * fderiv ℝ (u ∘ c.symm) (c x) (b j) := by
    erw [fderiv_fun_mul (hu'.differentiableAt (by norm_num))
      (hv'.differentiableAt (by norm_num))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Function.comp_apply]
    dsimp only [c] at hinv ⊢
    rw [hinv]
  have hd2 (i j : CoordIndex E) :
      fderiv ℝ (fun y => fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z)
        y (b j)) (c x) (b i) =
      u x * fderiv ℝ (fun y => fderiv ℝ (v ∘ c.symm) y (b j)) (c x) (b i) +
      v x * fderiv ℝ (fun y => fderiv ℝ (u ∘ c.symm) y (b j)) (c x) (b i) +
      fderiv ℝ (u ∘ c.symm) (c x) (b i) * fderiv ℝ (v ∘ c.symm) (c x) (b j) +
      fderiv ℝ (u ∘ c.symm) (c x) (b j) * fderiv ℝ (v ∘ c.symm) (c x) (b i) := by
    have he := second_fderiv_mul_at hu' hv' (b i) (b j)
    dsimp only [c] at hinv he ⊢
    simpa only [Function.comp_apply, hinv] using he
  simp_rw [hd2, hd1]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [← mul_assoc, hcross]
  unfold coordinateGradientPair
  dsimp only [c, b]
  simp only [← Finset.mul_sum, mul_assoc, mul_left_comm]
  ring

lemma weightedLaplacian_expansion {b u : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 b)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M) (x : M) :
    weightedLaplacian g b u x = b x * laplaceBeltrami g u x + coordinateGradientPair g b u x := by
  let c := chartAt E x
  let a := metricCoefficients g x
  let ρ := fun y => Real.sqrt (Matrix.det (a y))
  let e := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hb' := contDiffAt_inChart_C2 hb x hx
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hρ := Real.sqrt_pos.mpr (metricCoefficients_det_pos g x hx)
  have hρd := ((contDiffOn_metricDensity g x).contDiffAt ((chartAt E x).open_target.mem_nhds hx)).differentiableAt (by simp)
  have hflux (i : CoordIndex E) : DifferentiableAt ℝ
      (fun y => ρ y * ∑ j, (a y)⁻¹ i j * fderiv ℝ (u ∘ c.symm) y (e j)) (c x) := by
    apply hρd.mul
    apply DifferentiableAt.fun_sum
    intro j _
    apply (((contDiffOn_metricInverse g x i j).contDiffAt ((chartAt E x).open_target.mem_nhds hx)).differentiableAt (by simp)).mul
    exact ((hu'.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const _)
  change (ρ (c x))⁻¹ * ∑ i, fderiv ℝ
    (fun y => (b ∘ c.symm) y * (ρ y * ∑ j, (a y)⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) y (e j))) (c x) (e i) = _
  have hd (i : CoordIndex E) : fderiv ℝ
      (fun y => (b ∘ c.symm) y * (ρ y * ∑ j, (a y)⁻¹ i j *
        fderiv ℝ (u ∘ c.symm) y (e j))) (c x) (e i) =
      b x * fderiv ℝ (fun y => ρ y * ∑ j, (a y)⁻¹ i j *
        fderiv ℝ (u ∘ c.symm) y (e j)) (c x) (e i) +
      (ρ (c x) * ∑ j, (a (c x))⁻¹ i j * fderiv ℝ (u ∘ c.symm) (c x) (e j)) *
        fderiv ℝ (b ∘ c.symm) (c x) (e i) := by
    erw [fderiv_fun_mul (hb'.differentiableAt (by norm_num)) (hflux i)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Function.comp_apply]
    dsimp only [c] at hinv ⊢
    rw [hinv]
  simp_rw [hd, Finset.sum_add_distrib]
  change (ρ (c x))⁻¹ * ((∑ i, b x * _) +
    ∑ i, (ρ (c x) * ∑ j, (a (c x))⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) (c x) (e j)) *
        fderiv ℝ (b ∘ c.symm) (c x) (e i)) = _
  unfold laplaceBeltrami coordinateGradientPair
  dsimp only
  simp only [Finset.mul_sum, mul_add, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [ρ, a, c, e] at hρ ⊢
    field_simp [ne_of_gt hρ]

lemma weightedLaplacian_product_formula {b u : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 b)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M) (x : M) :
    weightedLaplacian g b u x =
      (laplaceBeltrami g (fun y => b y * u y) x + b x * laplaceBeltrami g u x -
        u x * laplaceBeltrami g b x) / 2 := by
  rw [weightedLaplacian_expansion hb hu, laplaceBeltrami_mul hb hu]
  ring


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
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma parametrixBound_nonneg : 0 ≤ A.parametrixBound := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (A.patchOutput i).opNorm_nonneg (mul_nonneg (A.localInverse i).bound_pos.le
    (metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k).opNorm_nonneg)

omit [T2Space M] in
lemma patchParametrix_bound (α : ℝ) (i : A.t)
    (hα : 1 ≤ α * (A.localInverse i).radius ^ 2) (u : A.H (2 * (k : ℝ))) :
    ‖A.patchParametrix α i hα u‖ ≤
      ‖A.patchOutput i‖ * ((A.localInverse i).bound *
        ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖) * ‖u‖ := by
  let R := metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα
  have hR : ‖R‖ ≤ (A.localInverse i).bound *
      ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ((A.localInverse i).norm_bound _ hα)
        (metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k).opNorm_nonneg)
  change ‖A.patchOutput i (R (u.val i))‖ ≤ _
  calc
    _ ≤ ‖A.patchOutput i‖ * (‖R‖ * ‖u.val i‖) :=
      ((A.patchOutput i).le_opNorm _).trans (mul_le_mul_of_nonneg_left (R.le_opNorm _) (A.patchOutput i).opNorm_nonneg)
    _ ≤ ‖A.patchOutput i‖ * (((A.localInverse i).bound *
        ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖) * ‖u‖) := by
      apply mul_le_mul_of_nonneg_left _ (A.patchOutput i).opNorm_nonneg
      exact mul_le_mul hR (norm_le_pi_norm u.val i) (norm_nonneg _) (R.opNorm_nonneg.trans hR)
    _ = _ := by ring

omit [T2Space M] in
lemma parametrix_bound (α : ℝ) (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (u : A.H (2 * (k : ℝ))) : ‖A.parametrix α hα u‖ ≤ A.parametrixBound * ‖u‖ := by
  calc
    _ ≤ ∑ i, ‖A.patchParametrix α i (hα i) u‖ := by
      simpa only [parametrix, sum_apply] using norm_sum_le _ _
    _ ≤ ∑ i, ‖A.patchOutput i‖ * ((A.localInverse i).bound *
        ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖) * ‖u‖ :=
      Finset.sum_le_sum (fun i _ => A.patchParametrix_bound α i (hα i) u)
    _ = _ := (Finset.sum_mul ..).symm

omit [T2Space M] in
lemma resolvent_bound (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (u : A.H (2 * (k : ℝ))) :
    ‖A.resolvent B α hα he u‖ ≤ 2 * A.parametrixBound * ‖u‖ := by
  have hN := neumannCorrectedInverse_bound
    (ContinuousLinearMap.id ℝ (A.H (2 * (k : ℝ)))) (A.error B α hα)
    (A.error_lt_one B α hα he) 1 ContinuousLinearMap.norm_id_le
    (by simpa only [one_mul] using (A.error_norm_bound B α hα).trans he) u
  apply (A.parametrix_bound α hα _).trans
  calc
    _ ≤ A.parametrixBound * (2 * 1 * ‖u‖) := mul_le_mul_of_nonneg_left hN A.parametrixBound_nonneg
    _ = _ := by ring

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
section SubspaceBilinear
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
lemma norm_restrict_of_bound (f : X →L[ℝ] Y) (S : Submodule ℝ X) (T : Submodule ℝ Y)
    (hf : ∀ x ∈ S, f x ∈ T) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.restrict hf‖ ≤ C := by
  apply (f.restrict hf).opNorm_le_bound hC
  intro x
  change ‖f (x : X)‖ ≤ C * ‖(x : X)‖
  exact hb (x : X)
end SubspaceBilinear
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

attribute [local instance] OAI.YauCounterexamples.CompactMetricAtlas.realH_smulCommClass
local instance realH_isScalarTower_rc60ad3_1 (s : ℝ) : IsScalarTower ℝ ℝ (A.realH s) :=
  ⟨fun a b c => mul_smul a b c⟩
local instance H_real_smulCommClass_rc60ad3_1 (s : ℝ) : SMulCommClass ℝ ℝ (A.H s) :=
  ⟨fun a b c => by simp only [smul_smul, mul_comm]⟩
local instance H_real_isScalarTower_rc60ad3_1 (s : ℝ) : IsScalarTower ℝ ℝ (A.H s) :=
  ⟨fun a b c => mul_smul a b c⟩
omit [T2Space M] in
lemma realProduct_representative (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (u v : A.realH (2 * (l : ℝ))) (x : M) :
    A.representative (2 * (l : ℝ)) (A.realProduct l ht u v) x =
      A.representative (2 * (l : ℝ)) u x * A.representative (2 * (l : ℝ)) v x :=
  A.product_representative l ht u v x

lemma realResolvent_norm_bound (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) (he : A.errorBound B α ≤ 1 / 2) :
    ‖A.realResolvent B α hα0 hα he‖ ≤ 2 * A.parametrixBound := by
  exact norm_restrict_of_bound (A.resolvent B α hα he) _ _ _ _ (mul_nonneg (by norm_num) A.parametrixBound_nonneg)
    (A.resolvent_bound B α hα he)

end CompactMetricAtlas

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma boundedDivergence_norm (p : X →L[ℝ] X →L[ℝ] X) (q : Y →L[ℝ] Y →L[ℝ] Y)
    (I L : X →L[ℝ] Y) (b : X) :
    ‖boundedDivergence p q I L b‖ ≤
      (‖L‖ * ‖p‖ + 2 * ‖q‖ * ‖I‖ * ‖L‖) / 2 * ‖b‖ := by
  rw [boundedDivergence, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * (‖L.comp (p b)‖ + ‖(q (I b)).comp L‖ + ‖(q (L b)).comp I‖) := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (1 / 2 : ℝ) * (‖L‖ * (‖p‖ * ‖b‖) +
        (‖q‖ * (‖I‖ * ‖b‖)) * ‖L‖ + (‖q‖ * (‖L‖ * ‖b‖)) * ‖I‖) := by
      gcongr
      · exact (L.opNorm_comp_le (p b)).trans (mul_le_mul_of_nonneg_left (p.le_opNorm b) (norm_nonneg _))
      · exact ((q (I b)).opNorm_comp_le L).trans (mul_le_mul_of_nonneg_right ((q.le_opNorm (I b)).trans (mul_le_mul_of_nonneg_left (I.le_opNorm b) (norm_nonneg _))) (norm_nonneg _))
      · exact ((q (L b)).opNorm_comp_le I).trans (mul_le_mul_of_nonneg_right ((q.le_opNorm (L b)).trans (mul_le_mul_of_nonneg_left (L.le_opNorm b) (norm_nonneg _))) (norm_nonneg _))
    _ = _ := by ring

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

local instance realH_smulCommClass'_rc60ad3_1 (s : ℝ) : SMulCommClass ℝ ℝ (A.realH s) :=
  ⟨fun a b c => by simp only [smul_smul, mul_comm]⟩
omit [T2Space M] in
lemma realValue_product (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (u v : A.realH (2 * (l : ℝ))) (x : M) :
    A.realValue (2 * (l : ℝ)) (A.realProduct l ht u v) x =
      A.realValue (2 * (l : ℝ)) u x * A.realValue (2 * (l : ℝ)) v x := by
  simpa only [realValue, Complex.mul_re, u.property x, zero_mul, sub_zero] using
    congrArg Complex.re (A.realProduct_representative l ht u v x)

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

omit [T2Space M] in
lemma realValue_laplacian (B : ∀ i, A.PatchCoefficients i)
    (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.realValue (2 * (k : ℝ)) (A.realLaplacian B u) x =
      laplaceBeltrami g (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  change (A.representative _ (A.laplacianCLM B u) x).re = _
  rw [A.laplacianCLM_representative]
  rfl

omit [T2Space M] in
lemma realDivergence_value (B : ∀ i, A.PatchCoefficients i)
    (b u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.realValue (2 * (k : ℝ)) (A.realDivergence B b u) x =
      weightedLaplacian g (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) b)
        (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  simp only [realDivergence, boundedDivergence, _root_.smul_apply,
    _root_.add_apply, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, A.realValue_smul, A.realValue_sub,
    A.realValue_add, A.realValue_product, A.realValue_inclusion, A.realValue_laplacian]
  rw [weightedLaplacian_product_formula (A.realValue_C2 b) (A.realValue_C2 u)]
  have hfun : A.realValue (2 * ((k + 1 : ℕ) : ℝ))
      (A.realProduct (k + 1) (by push_cast; linarith) b u) =
      fun y => A.realValue (2 * ((k + 1 : ℕ) : ℝ)) b y *
        A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u y := by
    funext y
    exact A.realValue_product _ _ b u y
  rw [hfun]
  ring

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

lemma laplaceBeltrami_const (g : SmoothMetric E M) (c : ℝ) (x : M) :
    laplaceBeltrami g (fun _ => c) x = 0 := by
  simp [laplaceBeltrami, Function.comp_def]

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

lemma laplaceBeltrami_sub {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun y => u y - v y) x =
      laplaceBeltrami g u x - laplaceBeltrami g v x := by
  have h := congrArg Complex.re (complexLaplaceBeltrami_sub
    (Complex.ofRealCLM.contMDiff.comp hu) (Complex.ofRealCLM.contMDiff.comp hv) g x)
  simpa only [complexLaplaceBeltrami, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
    Function.comp_def, Complex.ofRealCLM_apply, Pi.sub_apply] using h

lemma weightedLaplacian_shift {b h : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 b)
    (hh : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 h) (g : SmoothMetric E M) (x : M) :
    weightedLaplacian g b (fun y => 1 + h y) x =
      weightedLaplacian g (fun y => b y - 1) h x + laplaceBeltrami g h x := by
  rw [weightedLaplacian_product_formula (u := fun y => 1 + h y) hb (contMDiff_const.add hh),
    weightedLaplacian_product_formula (b := fun y => b y - 1) (hb.sub contMDiff_const) hh]
  have he1 : (fun y => b y * (1 + h y)) = fun y => b y + b y * h y := by
    funext y; ring
  have he2 : (fun y => (b y - 1) * h y) = fun y => b y * h y - h y := by
    funext y; ring
  rw [he1, he2, laplaceBeltrami_add (v := fun y => b y * h y) hb (hb.mul hh),
    laplaceBeltrami_sub (u := fun y => b y * h y) (hb.mul hh) hh, laplaceBeltrami_sub (v := fun _ => 1) hb contMDiff_const,
    laplaceBeltrami_add (u := fun _ => 1) contMDiff_const hh, laplaceBeltrami_const]
  ring

end

open Set Filter Function Manifold
open scoped Topology ContDiff



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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_RepresentedWeightedQuinticSmooth
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
namespace YauCounterexamples
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem represented_weighted_quintic_smooth (hd : Module.finrank ℝ E = 3)
    {b s u : M → ℝ} (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (hsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ s) (hpos : ∀ x, 0 < b x)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (Λ : ℝ)
    (he : ∀ x, weightedLaplacian g b u x = Λ * b x ^ 3 * u x ^ 5 - Λ * s x * u x)
    (v : A.H (2 * ((k + 1 : ℕ) : ℝ)))
    (hv : (A.representative (2 * ((k + 1 : ℕ) : ℝ)) v : M → ℂ) = fun x => (u x : ℂ)) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u := by
  let g' := conformalMetric g b hb hpos
  let B := (nonempty_compactMetricAtlas g' k hs).some
  have ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)) := by push_cast; linarith
  let v' := A.transferAcross B (k + 1) v
  have hv' : (B.representative (2 * ((k + 1 : ℕ) : ℝ)) v' : M → ℂ) = fun x => (u x : ℂ) := by
    change (B.representative _ (A.transferAcross B (k + 1) v) : M → ℂ) = _
    rw [A.transferAcross_representative B (k + 1) ht]
    exact hv
  have ha1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => -(Λ * s x / b x ^ 3)) :=
    ((contMDiff_const.mul hsmooth).div₀ (hb.pow 3) (fun x => pow_ne_zero 3 (hpos x).ne')).neg
  let a : Fin 6 → ManifoldSmoothFunctions E M := fun i =>
    if i = 1 then ⟨fun x => (-(Λ * s x / b x ^ 3) : ℝ), Complex.ofRealCLM.contMDiff.comp ha1⟩
    else if i = 5 then ⟨fun _ => (Λ : ℂ), contMDiff_const⟩
    else 0
  have he' (x : M) : complexLaplaceBeltrami g' (fun x => (u x : ℂ)) x =
      ∑ i, a i x * (u x : ℂ) ^ i.val := by
    rw [complexLaplaceBeltrami_ofReal]
    change (laplaceBeltrami (conformalMetric g b hb hpos) u x : ℂ) = _
    rw [conformalMetric_laplacian_three hd, he]
    simp only [a, Fin.sum_univ_succ]
    norm_num [Fin.ext_iff, ContMDiffMap.coe_zero, ContMDiffMap.coeFn_mk]
    simp only [↓reduceIte, ContMDiffMap.coeFn_mk, ContMDiffMap.coe_zero, Pi.zero_apply, mul_zero, add_zero]
    have hn : (b x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos x).ne'
    field_simp
    ring
  have hu' := B.represented_semilinear_solution_smooth a
    (Complex.ofRealCLM.contMDiff.comp hu) he' v' hv'
  have hr := Complex.reCLM.contMDiff.comp hu'
  exact hr
end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RealValueCubic
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
namespace YauCounterexamples.BoundedAlgebra
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

lemma norm_power (p : A →L[ℝ] A →L[ℝ] A) (e : A) {K U r : ℝ}
    (hK : ‖p‖ ≤ K) (hU : ‖e‖ ≤ U) (hr : 0 ≤ r) {x : A} (hx : ‖x‖ ≤ r) (n : ℕ) :
    ‖power p e x n‖ ≤ K ^ n * U * r ^ n := by
  have hK0 := (norm_nonneg p).trans hK
  have hU0 := (norm_nonneg e).trans hU
  induction n with
  | zero => simpa only [power, Nat.rec_zero, pow_zero, one_mul, mul_one] using hU
  | succ n ih =>
    change ‖p x (power p e x n)‖ ≤ _
    calc
      _ ≤ ‖p‖ * ‖x‖ * ‖power p e x n‖ := p.le_opNorm₂ _ _
      _ ≤ K * r * (K ^ n * U * r ^ n) := by gcongr
      _ = K ^ (n + 1) * U * r ^ (n + 1) := by ring

lemma power_difference (p : A →L[ℝ] A →L[ℝ] A) (e : A) {K U r : ℝ}
    (hK : ‖p‖ ≤ K) (hU : ‖e‖ ≤ U) (hr : 0 ≤ r) {x y : A}
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖power p e x (n + 1) - power p e y (n + 1)‖ ≤
      (n + 1 : ℝ) * K ^ (n + 1) * U * r ^ n * ‖x - y‖ := by
  have hK0 := (norm_nonneg p).trans hK
  have hU0 := (norm_nonneg e).trans hU
  induction n with
  | zero =>
    change ‖p x e - p y e‖ ≤ _
    rw [← sub_apply, ← map_sub]
    calc
      _ ≤ ‖p‖ * ‖x - y‖ * ‖e‖ := p.le_opNorm₂ _ _
      _ ≤ K * ‖x - y‖ * U := by gcongr
      _ = ((0 : ℕ) + 1 : ℝ) * K ^ (0 + 1) * U * r ^ 0 * ‖x - y‖ := by ring
  | succ n ih =>
    have hid : power p e x (n + 1 + 1) - power p e y (n + 1 + 1) =
        p x (power p e x (n + 1) - power p e y (n + 1)) +
        p (x - y) (power p e y (n + 1)) := by
      simp only [power, map_sub, sub_apply]
      abel
    rw [hid]
    calc
      _ ≤ ‖p‖ * ‖x‖ * ‖power p e x (n + 1) - power p e y (n + 1)‖ +
          ‖p‖ * ‖x - y‖ * ‖power p e y (n + 1)‖ :=
        (norm_add_le _ _).trans (add_le_add (p.le_opNorm₂ _ _) (p.le_opNorm₂ _ _))
      _ ≤ K * r * ((n + 1 : ℝ) * K ^ (n + 1) * U * r ^ n * ‖x - y‖) +
          K * ‖x - y‖ * (K ^ (n + 1) * U * r ^ (n + 1)) := by
        gcongr
        exact norm_power p e hK hU hr hy (n + 1)
      _ = (↑(n + 1) + 1 : ℝ) * K ^ (n + 1 + 1) * U * r ^ (n + 1) * ‖x - y‖ := by
        push_cast
        ring

lemma power_difference_small (p : A →L[ℝ] A →L[ℝ] A) (e : A) {K U δ : ℝ}
    (hK : ‖p‖ ≤ K) (hU : ‖e‖ ≤ U) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {x y : A}
    (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) (n : ℕ) :
    ‖power p e x (n + 2) - power p e y (n + 2)‖ ≤
      (n + 2 : ℝ) * K ^ (n + 2) * U * δ * ‖x - y‖ := by
  have hK0 := (norm_nonneg p).trans hK
  have hU0 := (norm_nonneg e).trans hU
  have hpow : δ ^ (n + 1) ≤ δ := by
    calc
      _ = δ * δ ^ n := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hδ hδ1) hδ
      _ = δ := mul_one _
  calc
    _ ≤ (↑(n + 1) + 1 : ℝ) * K ^ (n + 1 + 1) * U * δ ^ (n + 1) * ‖x - y‖ :=
      power_difference p e hK hU hδ hx hy (n + 1)
    _ = (n + 2 : ℝ) * K ^ (n + 2) * U * δ ^ (n + 1) * ‖x - y‖ := by push_cast; ring
    _ ≤ (n + 2 : ℝ) * K ^ (n + 2) * U * δ * ‖x - y‖ := by gcongr

lemma remainder_zero (p : A →L[ℝ] A →L[ℝ] A) (e : A) : remainder p e 0 = 0 := by
  have hz (n : ℕ) : power p e 0 (n + 1) = 0 := by
    change p 0 _ = 0
    simp
  simp only [remainder, hz, smul_zero, add_zero]

lemma remainder_lipschitz (p : A →L[ℝ] A →L[ℝ] A) (e : A) {K U δ : ℝ}
    (hK : ‖p‖ ≤ K) (hU : ‖e‖ ≤ U) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {x y : A}
    (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) :
    ‖remainder p e x - remainder p e y‖ ≤ remainderConstant K U * δ * ‖x - y‖ := by
  have hid : remainder p e x - remainder p e y =
      (10 : ℝ) • (power p e x 2 - power p e y 2) +
      (10 : ℝ) • (power p e x 3 - power p e y 3) +
      (5 : ℝ) • (power p e x 4 - power p e y 4) +
      (power p e x 5 - power p e y 5) := by simp only [remainder, smul_sub]; abel
  rw [hid]
  have hn (c : ℝ) (hc : 0 ≤ c) (v : A) : ‖c • v‖ = c * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  calc
    _ ≤ 10 * ‖power p e x 2 - power p e y 2‖ +
        10 * ‖power p e x 3 - power p e y 3‖ +
        5 * ‖power p e x 4 - power p e y 4‖ + ‖power p e x 5 - power p e y 5‖ := by
      calc
        _ ≤ ‖(10 : ℝ) • (power p e x 2 - power p e y 2) +
          (10 : ℝ) • (power p e x 3 - power p e y 3) +
          (5 : ℝ) • (power p e x 4 - power p e y 4)‖ +
          ‖power p e x 5 - power p e y 5‖ := norm_add_le _ _
        _ ≤ (‖(10 : ℝ) • (power p e x 2 - power p e y 2) +
          (10 : ℝ) • (power p e x 3 - power p e y 3)‖ +
          ‖(5 : ℝ) • (power p e x 4 - power p e y 4)‖) +
          ‖power p e x 5 - power p e y 5‖ := by gcongr; exact norm_add_le _ _
        _ ≤ (‖(10 : ℝ) • (power p e x 2 - power p e y 2)‖ +
          ‖(10 : ℝ) • (power p e x 3 - power p e y 3)‖ +
          ‖(5 : ℝ) • (power p e x 4 - power p e y 4)‖) +
          ‖power p e x 5 - power p e y 5‖ := by gcongr; exact norm_add_le _ _
        _ = _ := by rw [hn 10 (by norm_num), hn 10 (by norm_num), hn 5 (by norm_num)]
    _ ≤ 10 * (2 * K ^ 2 * U * δ * ‖x - y‖) +
        10 * (3 * K ^ 3 * U * δ * ‖x - y‖) +
        5 * (4 * K ^ 4 * U * δ * ‖x - y‖) + 5 * K ^ 5 * U * δ * ‖x - y‖ := by
      gcongr
      · have h := power_difference_small p e hK hU hδ hδ1 hx hy 0
        norm_num at h
        exact h
      · have h := power_difference_small p e hK hU hδ hδ1 hx hy 1
        norm_num at h
        exact h
      · have h := power_difference_small p e hK hU hδ hδ1 hx hy 2
        norm_num at h
        exact h
      · have h := power_difference_small p e hK hU hδ hδ1 hx hy 3
        norm_num at h
        exact h
    _ = remainderConstant K U * δ * ‖x - y‖ := by unfold remainderConstant; ring

lemma polynomial_zero_bound (p : A →L[ℝ] A →L[ℝ] A) (e : A) {c s : A} {ε C : ℝ}
    (hc : ‖c - e‖ ≤ C * ε) (hs : ‖s - e‖ ≤ ε) :
    ‖polynomial p e c s 0‖ ≤ (C + 1) * ε := by
  simp only [polynomial, map_zero, remainder_zero, add_zero]
  have hid : c - s = (c - e) - (s - e) := by abel
  rw [hid]
  calc
    _ ≤ ‖c - e‖ + ‖s - e‖ := norm_sub_le _ _
    _ ≤ C * ε + ε := add_le_add hc hs
    _ = (C + 1) * ε := by ring

lemma polynomial_lipschitz (p : A →L[ℝ] A →L[ℝ] A) (e : A) {K U ε δ C V : ℝ}
    (hK : ‖p‖ ≤ K) (hU : ‖e‖ ≤ U) {c s : A}
    (hc : ‖c - e‖ ≤ C * ε) (hs : ‖s - e‖ ≤ ε) (hc' : ‖c‖ ≤ V)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {x y : A} (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) :
    ‖polynomial p e c s x - polynomial p e c s y‖ ≤
      (K * (5 * C + 1) * ε + K * V * remainderConstant K U * δ) * ‖x - y‖ := by
  have hK0 := (norm_nonneg p).trans hK
  have hV0 := (norm_nonneg c).trans hc'
  have hlin : ‖(5 : ℝ) • (c - e) - (s - e)‖ ≤ (5 * C + 1) * ε := by
    calc
      _ ≤ ‖(5 : ℝ) • (c - e)‖ + ‖s - e‖ := norm_sub_le _ _
      _ = 5 * ‖c - e‖ + ‖s - e‖ := by rw [norm_smul]; norm_num
      _ ≤ 5 * (C * ε) + ε := by gcongr
      _ = (5 * C + 1) * ε := by ring
  have hid : polynomial p e c s x - polynomial p e c s y =
      p ((5 : ℝ) • (c - e) - (s - e)) (x - y) + p c (remainder p e x - remainder p e y) := by
    simp only [polynomial, map_sub]
    abel
  rw [hid]
  calc
    _ ≤ ‖p‖ * ‖(5 : ℝ) • (c - e) - (s - e)‖ * ‖x - y‖ +
        ‖p‖ * ‖c‖ * ‖remainder p e x - remainder p e y‖ :=
      (norm_add_le _ _).trans (add_le_add (p.le_opNorm₂ _ _) (p.le_opNorm₂ _ _))
    _ ≤ K * ((5 * C + 1) * ε) * ‖x - y‖ +
        K * V * (remainderConstant K U * δ * ‖x - y‖) := by
      gcongr
      exact remainder_lipschitz p e hK hU hδ hδ1 hx hy
    _ = (K * (5 * C + 1) * ε + K * V * remainderConstant K U * δ) * ‖x - y‖ := by ring

variable [CompleteSpace A]
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem solve (R : B →L[ℝ] A) (I D : A →L[ℝ] B) (P : A → A)
    (Λ δ L Z : ℝ) (hΛ : 0 ≤ Λ) (hδ : 0 ≤ δ)
    (hP : ∀ x y, ‖x‖ ≤ δ → ‖y‖ ≤ δ → ‖P x - P y‖ ≤ L * ‖x - y‖)
    (hP0 : ‖P 0‖ ≤ Z)
    (hsmall : ‖R‖ * (‖D‖ + Λ * ‖I‖ * L) ≤ 1 / 2)
    (hstart : ‖R‖ * Λ * ‖I‖ * Z ≤ δ / 2) :
    ∃ h : A, ‖h‖ ≤ δ ∧ h = R (D h - Λ • I (P h)) := by
  let T : A → A := fun h => R (D h - Λ • I (P h))
  have hTlip (x y : A) (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) :
      ‖T x - T y‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ := by
    have hid : T x - T y = R (D (x - y) - Λ • I (P x - P y)) := by
      simp only [T, map_sub, smul_sub]; abel
    rw [hid]
    calc
      _ ≤ ‖R‖ * ‖D (x - y) - Λ • I (P x - P y)‖ := R.le_opNorm _
      _ ≤ ‖R‖ * (‖D‖ * ‖x - y‖ + Λ * (‖I‖ * ‖P x - P y‖)) := by
        gcongr
        calc
          _ ≤ ‖D (x - y)‖ + ‖Λ • I (P x - P y)‖ := norm_sub_le _ _
          _ = ‖D (x - y)‖ + Λ * ‖I (P x - P y)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hΛ]
          _ ≤ _ := add_le_add (D.le_opNorm _) (mul_le_mul_of_nonneg_left (I.le_opNorm _) hΛ)
      _ ≤ ‖R‖ * (‖D‖ * ‖x - y‖ + Λ * (‖I‖ * (L * ‖x - y‖))) := by
        gcongr
        exact hP x y hx hy
      _ = (‖R‖ * (‖D‖ + Λ * ‖I‖ * L)) * ‖x - y‖ := by ring
      _ ≤ (1 / 2 : ℝ) * ‖x - y‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  have hTzero : ‖T 0‖ ≤ δ / 2 := by
    simp only [T, map_zero, zero_sub, map_neg, norm_neg]
    calc
      _ ≤ ‖R‖ * ‖Λ • I (P 0)‖ := R.le_opNorm _
      _ = ‖R‖ * (Λ * ‖I (P 0)‖) := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hΛ]
      _ ≤ ‖R‖ * (Λ * (‖I‖ * Z)) := by gcongr; exact (I.le_opNorm _).trans (by gcongr)
      _ = ‖R‖ * Λ * ‖I‖ * Z := by ring
      _ ≤ δ / 2 := hstart
  let S : Set A := Metric.closedBall 0 δ
  have hS : ∀ x : A, x ∈ S ↔ ‖x‖ ≤ δ := by intro x; simp [S, dist_eq_norm]
  have hmaps : MapsTo T S S := by
    intro x hx
    apply (hS _).2
    calc
      ‖T x‖ ≤ ‖T x - T 0‖ + ‖T 0‖ := norm_le_norm_sub_add _ _
      _ ≤ (1 / 2 : ℝ) * ‖x - 0‖ + δ / 2 :=
        add_le_add (hTlip x 0 ((hS _).1 hx) (by simpa using hδ)) hTzero
      _ ≤ δ := by simpa only [sub_zero] using (by linarith [(hS _).1 hx] :
        (1 / 2 : ℝ) * ‖x‖ + δ / 2 ≤ δ)
  have hcontract : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict T S S) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (T x.val) (T y.val) ≤ ((1 / 2 : ℝ≥0) : ℝ) * dist x.val y.val
    simp only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    exact hTlip x y ((hS _).1 x.property) ((hS _).1 y.property)
  have hcomplete : IsComplete S := Metric.isClosed_closedBall.isComplete
  obtain ⟨h, hh, hfixed, -, -⟩ := hcontract.exists_fixedPoint' hcomplete hmaps
    ((hS 0).2 (by simpa using hδ)) (edist_ne_top 0 (T 0))
  exact ⟨h, (hS _).1 hh, hfixed.symm⟩
end YauCounterexamples.BoundedAlgebra

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
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
lemma realValue_norm_bound (s : ℝ) (u : A.realH s) (x : M) :
    |A.realValue s u x| ≤ ‖A.representative s‖ * ‖u‖ :=
  (Complex.abs_re_le_norm _).trans (((A.representative s u).norm_coe_le_norm x).trans
    ((A.representative s).le_opNorm u))

local instance realH_smulCommClass_fp_rc60ad3_1 (s : ℝ) : SMulCommClass ℝ ℝ (A.realH s) :=
  ⟨fun a b c => by simp only [smul_smul, mul_comm]⟩
omit [T2Space M] in
lemma realValue_power (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (e h : A.realH (2 * (l : ℝ))) (he : ∀ x, A.realValue (2 * (l : ℝ)) e x = 1)
    (n : ℕ) (x : M) :
    A.realValue (2 * (l : ℝ)) (BoundedAlgebra.power (A.realProduct l ht) e h n) x =
      A.realValue (2 * (l : ℝ)) h x ^ n := by
  induction n with
  | zero => exact (he x).trans (pow_zero _).symm
  | succ n ih =>
    change A.realValue _ (A.realProduct l ht h (BoundedAlgebra.power (A.realProduct l ht) e h n)) x = _
    rw [A.realValue_product, ih, pow_succ]
    exact mul_comm _ _

omit [T2Space M] in
lemma realValue_polynomial (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (e c s h : A.realH (2 * (l : ℝ))) (he : ∀ x, A.realValue (2 * (l : ℝ)) e x = 1)
    (x : M) :
    A.realValue (2 * (l : ℝ)) (BoundedAlgebra.polynomial (A.realProduct l ht) e c s h) x =
      A.realValue (2 * (l : ℝ)) c x * (1 + A.realValue (2 * (l : ℝ)) h x) ^ 5 -
        A.realValue (2 * (l : ℝ)) s x * (1 + A.realValue (2 * (l : ℝ)) h x) -
          4 * A.realValue (2 * (l : ℝ)) h x := by
  simp only [BoundedAlgebra.polynomial, BoundedAlgebra.remainder, A.realValue_sub,
    A.realValue_add, A.realValue_smul, A.realValue_product, A.realValue_power l ht e h he, he]
  ring

end CompactMetricAtlas
end YauCounterexamples

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
namespace YauCounterexamples
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

attribute [local instance] OAI.YauCounterexamples.CompactMetricAtlas.realH_smulCommClass_pf
local instance realH_isScalarTower_pf_rc60ad3_1 (s : ℝ) : IsScalarTower ℝ ℝ (A.realH s) :=
  ⟨fun a b c => mul_smul a b c⟩
theorem exists_positive_factor_of_bounds
    (hd : Module.finrank ℝ E = 3) (B : ∀ i, A.PatchCoefficients i)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)))
    (b s : M → ℝ) (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (hsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ s) (hbpos : ∀ x, 0 < b x)
    (e c σ β : A.realH (2 * ((k + 1 : ℕ) : ℝ)))
    (he : ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) e x = 1)
    (hc : ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) c x = b x ^ 3)
    (hσ : ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) σ x = s x)
    (hβ : ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) β x = b x - 1)
    (Λ δ K U ε C V : ℝ) (hΛ : 0 < Λ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hK : ‖A.realProduct (k + 1) ht‖ ≤ K) (hU : ‖e‖ ≤ U)
    (hcsmall : ‖c - e‖ ≤ C * ε) (hσsmall : ‖σ - e‖ ≤ ε) (hcsize : ‖c‖ ≤ V)
    (hα : ∀ i, 1 ≤ 4 * Λ * (A.localInverse i).radius ^ 2)
    (herr : A.errorBound B (4 * Λ) ≤ 1 / 2)
    (hsmall : ‖A.realResolvent B (4 * Λ) (by positivity) hα herr‖ *
      (‖A.realDivergence B β‖ + Λ * ‖A.realInclusion‖ *
        (K * (5 * C + 1) * ε + K * V * BoundedAlgebra.remainderConstant K U * δ)) ≤ 1 / 2)
    (hstart : ‖A.realResolvent B (4 * Λ) (by positivity) hα herr‖ * Λ *
      ‖A.realInclusion‖ * ((C + 1) * ε) ≤ δ / 2)
    (hpositive : ‖A.representative (2 * ((k + 1 : ℕ) : ℝ))‖ * δ < 1) :
    ∃ u : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u ∧ (∀ x, 0 < u x) ∧
      (∀ x, weightedLaplacian g b u x = Λ * b x ^ 3 * u x ^ 5 - Λ * s x * u x) ∧
      (∀ x, |u x - 1| ≤ ‖A.representative (2 * ((k + 1 : ℕ) : ℝ))‖ * δ) ∧
      ∃ h : A.realH (2 * ((k + 1 : ℕ) : ℝ)), ‖h‖ ≤ δ ∧
        ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) h x = u x - 1 := by
  let p := A.realProduct (k + 1) ht
  let P := BoundedAlgebra.polynomial p e c σ
  let R := A.realResolvent B (4 * Λ) (by positivity) hα herr
  have hp (x y : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) :
      ‖P x - P y‖ ≤ (K * (5 * C + 1) * ε + K * V * BoundedAlgebra.remainderConstant K U * δ) * ‖x - y‖ :=
    BoundedAlgebra.polynomial_lipschitz p e hK hU hcsmall hσsmall hcsize hδ hδ1 hx hy
  have hp0 : ‖P 0‖ ≤ (C + 1) * ε := BoundedAlgebra.polynomial_zero_bound p e hcsmall hσsmall
  obtain ⟨h, hh, hfixed⟩ := BoundedAlgebra.solve R A.realInclusion (A.realDivergence B β) P
    Λ δ _ _ hΛ.le hδ hp hp0 hsmall hstart
  let u : M → ℝ := fun x => 1 + A.realValue (2 * ((k + 1 : ℕ) : ℝ)) h x
  have hu2 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u := contMDiff_const.add (A.realValue_C2 h)
  have hub (x : M) : |u x - 1| ≤ ‖A.representative (2 * ((k + 1 : ℕ) : ℝ))‖ * δ := by
    dsimp only [u]
    rw [add_sub_cancel_left]
    have hn : 0 ≤ ‖A.representative (2 * ((k + 1 : ℕ) : ℝ))‖ := (A.representative (2 * ((k + 1 : ℕ) : ℝ))).opNorm_nonneg
    exact (A.realValue_norm_bound _ h x).trans (mul_le_mul_of_nonneg_left hh hn)
  have hup (x : M) : 0 < u x := by
    have h := (abs_le.mp (hub x)).1
    linarith
  have heq (x : M) : weightedLaplacian g b u x = Λ * b x ^ 3 * u x ^ 5 - Λ * s x * u x := by
    have hres := A.realResolvent_value B (4 * Λ) (by positivity) hα herr
      (A.realDivergence B β h - Λ • A.realInclusion (P h)) x
    change (4 * Λ) * A.realValue _ (R _) x - laplaceBeltrami g (A.realValue _ (R _)) x = _ at hres
    rw [← hfixed] at hres
    simp only [A.realValue_sub, A.realValue_smul, A.realValue_inclusion,
      A.realDivergence_value] at hres
    have hpv := A.realValue_polynomial (k + 1) ht e c σ h he x
    change A.realValue _ (P h) x = _ at hpv
    rw [hpv, hc, hσ] at hres
    have hβfun : A.realValue (2 * ((k + 1 : ℕ) : ℝ)) β = fun y => b y - 1 := funext hβ
    rw [hβfun] at hres
    dsimp only [u]
    rw [weightedLaplacian_shift (hb.of_le (by decide)) (A.realValue_C2 h)]
    linear_combination -hres
  have hv : (A.representative (2 * ((k + 1 : ℕ) : ℝ)) ((e + h : A.realH _).val) : M → ℂ) =
      fun x => (u x : ℂ) := by
    funext x
    rw [← A.ofReal_realValue, A.realValue_add, he]
  have husmooth := A.represented_weighted_quintic_smooth hd hb hsmooth hbpos hu2 Λ heq
    ((e + h : A.realH _).val) hv
  exact ⟨u, husmooth, hup, heq, hub, h, hh, fun x => by dsimp [u]; ring⟩

end CompactMetricAtlas
end YauCounterexamples

end

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
namespace YauCounterexamples.BoundedAlgebra
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma cubicPerturbation_bound (p : X →L[ℝ] X →L[ℝ] X) (e : X) {K U ε : ℝ}
    (hK : ‖p‖ ≤ K) (hU : ‖e‖ ≤ U) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {x : X} (hx : ‖x‖ ≤ ε) :
    ‖cubicPerturbation p e x - e‖ ≤ (3 + 3 * K ^ 2 * U + K ^ 3 * U) * ε := by
  have hK0 := (norm_nonneg p).trans hK
  have hU0 := (norm_nonneg e).trans hU
  have hpow (n : ℕ) : ε ^ (n + 1) ≤ ε := by
    calc ε ^ (n + 1) = ε * ε ^ n := by ring
         _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hε hε1) hε
         _ = ε := mul_one _
  have h2 := norm_power p e hK hU hε hx 2
  have h3 := norm_power p e hK hU hε hx 3
  have h2' : ‖power p e x 2‖ ≤ K ^ 2 * U * ε :=
    h2.trans (mul_le_mul_of_nonneg_left (hpow 1) (by positivity))
  have h3' : ‖power p e x 3‖ ≤ K ^ 3 * U * ε :=
    h3.trans (mul_le_mul_of_nonneg_left (hpow 2) (by positivity))
  have heq : cubicPerturbation p e x - e =
      (3 : ℝ) • x + (3 : ℝ) • power p e x 2 + power p e x 3 := by
    unfold cubicPerturbation
    abel
  rw [heq]
  calc
    _ ≤ (‖(3 : ℝ) • x‖ + ‖(3 : ℝ) • power p e x 2‖) + ‖power p e x 3‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = 3 * ‖x‖ + 3 * ‖power p e x 2‖ + ‖power p e x 3‖ := by
      rw [norm_smul, norm_smul]; norm_num
    _ ≤ 3 * ε + 3 * (K ^ 2 * U * ε) + K ^ 3 * U * ε := by gcongr
    _ = _ := by ring
end YauCounterexamples.BoundedAlgebra

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
namespace YauCounterexamples
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

lemma realValue_cubic (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (e h : A.realH (2 * (l : ℝ))) (he : ∀ x, A.realValue (2 * (l : ℝ)) e x = 1)
    (x : M) :
    A.realValue (2 * (l : ℝ)) (BoundedAlgebra.cubicPerturbation (A.realProduct l ht) e h) x =
      (1 + A.realValue (2 * (l : ℝ)) h x) ^ 3 := by
  simp only [BoundedAlgebra.cubicPerturbation, A.realValue_add, A.realValue_smul,
    A.realValue_power l ht e h he, he]
  ring

lemma realDivergence_norm_bound (B : ∀ i, A.PatchCoefficients i)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)))
    (b : A.realH (2 * ((k + 1 : ℕ) : ℝ))) :
    ‖A.realDivergence B b‖ ≤
      (‖A.realLaplacian B‖ * ‖A.realProduct (k + 1) ht‖ +
        2 * ‖A.realProduct k hs‖ * ‖A.realInclusion‖ * ‖A.realLaplacian B‖) / 2 * ‖b‖ :=
  boundedDivergence_norm _ _ _ _ _
end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CubicConstantNonneg
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
namespace YauCounterexamples
open Filter
open scoped Topology ContDiff Manifold
private lemma cubicConstant_nonneg {K U : ℝ} (hK : 0 ≤ K) (hU : 0 ≤ U) :
    0 ≤ 3 + 3 * K ^ 2 * U + K ^ 3 * U := by positivity
private lemma quinticConstant_nonneg {K U : ℝ} (hK : 0 ≤ K) (hU : 0 ≤ U) :
    0 ≤ BoundedAlgebra.remainderConstant K U := by
  unfold BoundedAlgebra.remainderConstant
  positivity
private lemma factor_limit_algebra (Λ ε δ : ℕ → ℝ) (R D I K C V F : ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hΛε : Tendsto (fun n => Λ n * ε n) atTop (𝓝 0))
    (hΛδ : Tendsto (fun n => Λ n * δ n) atTop (𝓝 0))
    (hstart : Tendsto (fun n => Λ n * ε n / δ n) atTop (𝓝 0)) :
    Tendsto (fun n => R * (D * ε n + Λ n * I *
      (K * (5 * C + 1) * ε n + K * V * F * δ n))) atTop (𝓝 0) ∧
    Tendsto (fun n => R * Λ n * I * ((C + 1) * ε n) / δ n) atTop (𝓝 0) := by
  constructor
  · convert ((hε.const_mul (R * D)).add
      ((hΛε.const_mul (R * I * K * (5 * C + 1))).add
        (hΛδ.const_mul (R * I * K * V * F)))) using 1
    · ext n; ring
    · simp
  · convert hstart.const_mul (R * I * (C + 1)) using 1
    · ext n; ring
    · simp
private lemma norm_le_of_sub_bound {X : Type*} [NormedAddCommGroup X]
    (c e : X) (C ε : ℝ) (hC : 0 ≤ C) (hε : ε ≤ 1) (hc : ‖c - e‖ ≤ C * ε) :
    ‖c‖ ≤ ‖e‖ + C := by
  calc
    ‖c‖ ≤ ‖c - e‖ + ‖e‖ := by simpa using norm_add_le (c - e) e
    _ ≤ C * ε + ‖e‖ := add_le_add hc le_rfl
    _ ≤ C * 1 + ‖e‖ := add_le_add (mul_le_mul_of_nonneg_left hε hC) le_rfl
    _ = ‖e‖ + C := by ring
private lemma factor_bound_transfer {r R d D Λ I K C V F ε δ : ℝ}
    (hR : 0 ≤ R) (hd0 : 0 ≤ d) (hΛ : 0 ≤ Λ) (hI : 0 ≤ I)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hV : 0 ≤ V) (hF : 0 ≤ F)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hr : r ≤ R) (hd : d ≤ D * ε) :
    r * (d + Λ * I * (K * (5 * C + 1) * ε + K * V * F * δ)) ≤
      R * (D * ε + Λ * I * (K * (5 * C + 1) * ε + K * V * F * δ)) ∧
    r * Λ * I * ((C + 1) * ε) ≤ R * Λ * I * ((C + 1) * ε) := by
  constructor
  · exact mul_le_mul hr (add_le_add hd le_rfl) (by positivity) hR
  · gcongr
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem eventually_positive_factor_oai
    (hd : Module.finrank ℝ E = 3) (B : ∀ i, A.PatchCoefficients i)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)))
    (b s : ℕ → M → ℝ)
    (hb : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (b n))
    (hsmooth : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (s n))
    (Λ ε δ : ℕ → ℝ)
    (hΛ : Tendsto Λ atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hΛε : Tendsto (fun n => Λ n * ε n) atTop (𝓝 0))
    (hΛδ : Tendsto (fun n => Λ n * δ n) atTop (𝓝 0))
    (hstart : Tendsto (fun n => Λ n * ε n / δ n) atTop (𝓝 0))
    (hpos : ∀ᶠ n in atTop, 0 ≤ ε n ∧ 0 < δ n)
    (hdata : ∀ᶠ n in atTop,
      ‖A.realOfSmooth _ ht (fun x => b n x - 1) ((hb n).sub contMDiff_const)‖ ≤ ε n ∧
      ‖A.realOfSmooth _ ht (fun x => s n x - 1) ((hsmooth n).sub contMDiff_const)‖ ≤ ε n) :
    ∀ᶠ n in atTop, ∃ u : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u ∧ (∀ x, 0 < u x) ∧
      (∀ x, weightedLaplacian g (b n) u x =
        Λ n * b n x ^ 3 * u x ^ 5 - Λ n * s n x * u x) ∧
      ∃ h : A.realH (2 * ((k + 1 : ℕ) : ℝ)), ‖h‖ ≤ δ n ∧
        ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) h x = u x - 1 := by
  let q : ℝ := 2 * ((k + 1 : ℕ) : ℝ)
  let e := A.realOfSmooth q ht (fun _ => 1) contMDiff_const
  let U := ‖e‖
  let K := ‖A.realProduct (k + 1) ht‖
  let C := 3 + 3 * K ^ 2 * U + K ^ 3 * U
  let V := U + C
  let R := 2 * A.parametrixBound
  let I := ‖A.realInclusion‖
  let J := ‖A.representative q‖
  let D := (‖A.realLaplacian B‖ * K +
    2 * ‖A.realProduct k hs‖ * I * ‖A.realLaplacian B‖) / 2
  let F := BoundedAlgebra.remainderConstant K U
  have hU : 0 ≤ U := norm_nonneg e
  have hK : 0 ≤ K := (A.realProduct (k + 1) ht).opNorm_nonneg
  have hC : 0 ≤ C := cubicConstant_nonneg hK hU
  have hV : 0 ≤ V := add_nonneg hU hC
  have hR : 0 ≤ R := mul_nonneg (by norm_num) A.parametrixBound_nonneg
  have hI : 0 ≤ I := A.realInclusion.opNorm_nonneg
  have hJ : 0 ≤ J := (A.representative q).opNorm_nonneg
  have hL : 0 ≤ ‖A.realLaplacian B‖ := (A.realLaplacian B).opNorm_nonneg
  have hlow : 0 ≤ ‖A.realProduct k hs‖ := (A.realProduct k hs).opNorm_nonneg
  have hD : 0 ≤ D := div_nonneg (add_nonneg (mul_nonneg hL hK)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlow) hI) hL)) (by norm_num)
  have hF : 0 ≤ F := quinticConstant_nonneg hK hU
  obtain ⟨hsmalllim, hstartlim⟩ := factor_limit_algebra Λ ε δ R D I K C V F hε hΛε hΛδ hstart
  have hJε : Tendsto (fun n => J * ε n) atTop (𝓝 0) := by simpa using hε.const_mul J
  have hJδ : Tendsto (fun n => J * δ n) atTop (𝓝 0) := by simpa using hδ.const_mul J
  obtain ⟨a, ha, hadm⟩ := A.exists_parametrix_threshold B
  have hmass : Tendsto (fun n => 4 * Λ n) atTop atTop := Filter.Tendsto.const_mul_atTop (by norm_num) hΛ
  filter_upwards [hpos, hdata, hΛ.eventually (eventually_gt_atTop 0),
    hmass.eventually (eventually_ge_atTop a),
    hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hδ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hsmalllim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hstartlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hJε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hJδ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hn hdatan hΛn ham hεn hδn hsmalln hstartn hJεn hJδn
  let β := A.realOfSmooth q ht (fun x => b n x - 1) ((hb n).sub contMDiff_const)
  let τ := A.realOfSmooth q ht (fun x => s n x - 1) ((hsmooth n).sub contMDiff_const)
  let σ := e + τ
  let c := BoundedAlgebra.cubicPerturbation (A.realProduct (k + 1) ht) e β
  have he (x : M) : A.realValue q e x = 1 := A.realOfSmooth_value q ht _ _ x
  have hβ (x : M) : A.realValue q β x = b n x - 1 := A.realOfSmooth_value q ht _ _ x
  have hσ (x : M) : A.realValue q σ x = s n x := by
    dsimp only [σ]
    rw [A.realValue_add, he, A.realOfSmooth_value]
    ring
  have hc (x : M) : A.realValue q c x = b n x ^ 3 := by
    dsimp only [c]
    rw [A.realValue_cubic (k + 1) ht e β he, hβ]
    ring
  have hce : ‖c - e‖ ≤ C * ε n :=
    BoundedAlgebra.cubicPerturbation_bound _ e le_rfl le_rfl hn.1 hεn.le hdatan.1
  have hcs : ‖c‖ ≤ V := norm_le_of_sub_bound c e C (ε n) hC hεn.le hce
  have hσe : ‖σ - e‖ ≤ ε n := by
    have hm : σ - e = τ := by dsimp [σ]; abel
    rw [hm]
    exact hdatan.2
  have hbpos (x : M) : 0 < b n x := by
    have hv := A.realValue_norm_bound q β x
    rw [hβ] at hv
    have hv' : |b n x - 1| < 1 := (hv.trans
      (mul_le_mul_of_nonneg_left hdatan.1 hJ)).trans_lt hJεn
    have := (abs_lt.mp hv').1
    linarith
  obtain ⟨hα, herr⟩ := hadm _ ham
  have hRn : ‖A.realResolvent B (4 * Λ n) (by positivity) hα herr‖ ≤ R :=
    A.realResolvent_norm_bound B _ (by positivity) hα herr
  have hDn : ‖A.realDivergence B β‖ ≤ D * ε n :=
    (A.realDivergence_norm_bound B ht β).trans (mul_le_mul_of_nonneg_left hdatan.1 hD)
  have hdn0 : 0 ≤ ‖A.realDivergence B β‖ := (A.realDivergence B β).opNorm_nonneg
  obtain ⟨hbound, hboundstart⟩ := factor_bound_transfer hR hdn0 hΛn.le hI hK hC hV hF
    hn.1 hn.2.le hRn hDn
  have hsmall' := hbound.trans hsmalln.le
  have hstart' : ‖A.realResolvent B (4 * Λ n) (by positivity) hα herr‖ * Λ n * I *
      ((C + 1) * ε n) ≤ δ n / 2 := by
    calc
      _ ≤ R * Λ n * I * ((C + 1) * ε n) := hboundstart
      _ ≤ (1 / 2) * δ n := (div_le_iff₀ hn.2).mp hstartn.le
      _ = δ n / 2 := by ring
  obtain ⟨u, hu, hup, hueq, _, h, hnorm, hv⟩ := A.exists_positive_factor_of_bounds hd B ht
    (b n) (s n) (hb n) (hsmooth n) hbpos e c σ β he hc hσ hβ
    (Λ n) (δ n) K U (ε n) C V hΛn hn.2.le hδn.le le_rfl le_rfl hce hσe hcs
    hα herr hsmall' hstart' hJδn
  exact ⟨u, hu, hup, hueq, h, hnorm, hv⟩
end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.CompactMetricAtlas.eventually_positive_factor_oai.{u_1, u_2} := @OAI.YauCounterexamples.CompactMetricAtlas.eventually_positive_factor_oai.{u_1, u_2}
