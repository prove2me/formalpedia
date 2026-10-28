-- Prove2me | solution 1 for OAI.YauCounterexamples.proportional_eigen_global
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:23:46.272869+00:00
-- url     : https://prove2.me/submissions/43aa711b-6a8c-418e-8397-be7c854ca17f

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_exists_local_weighted_carleman

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_TestDerivativeComm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (K : Compacts E)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma testPair_integrable (f g : EllipticTest K) :
    Integrable (fun x => f x * g x) (volume : Measure E) :=
  (f.contDiff.continuous.mul g.contDiff.continuous).integrable_of_hasCompactSupport
    (f.compact_supp.mul_right)

end

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_DistanceSquare
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] (e : ι → E)

lemma SmoothScalar.sum_apply {κ : Type*} (s : Finset κ) (f : κ → SmoothScalar E) (x : E) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Subalgebra.coe_zero, Pi.zero_apply]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Subalgebra.coe_add, Pi.add_apply, ih]


end

open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma distanceSquare_derivative_center (x₀ v : E) :
    SmoothScalar.directional v (distanceSquare x₀) x₀ = 0 := by
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) x₀).sub_const x₀).norm_sq
  simp only [id_eq] at hd
  change fderiv ℝ (fun x => ‖x-x₀‖^2) x₀ v = _
  rw [hd.fderiv]
  simp

lemma tangentPhase_at (ψ : SmoothScalar E) (x₀ : E) (hψ : ψ x₀ = 0) : tangentPhase ψ x₀ x₀ = 0 := by
  simp [tangentPhase, hψ]
lemma tangentPhase_derivative_center (ψ : SmoothScalar E) (x₀ v : E) :
    SmoothScalar.directional v (tangentPhase ψ x₀) x₀ = SmoothScalar.directional v ψ x₀ := by
  change SmoothScalar.directional v (ψ - distanceSquare x₀) x₀ = _
  rw [map_sub]
  change SmoothScalar.directional v ψ x₀ - SmoothScalar.directional v (distanceSquare x₀) x₀ = _
  rw [distanceSquare_derivative_center, sub_zero]

lemma tangentPhase_annular_gap (ψ : SmoothScalar E) (x₀ x : E) (r H : ℝ)
    (hr : 0 < r) (hψ : ψ x ≤ 0) (hd : r/2 ≤ dist x x₀)
    (hsmall : -1 < H * tangentPhase ψ x₀ x) :
    convexifyPhase (tangentPhase ψ x₀) H x ≤ -r^2/8 := by
  have hnorm : r/2 ≤ ‖x-x₀‖ := by simpa only [dist_eq_norm] using hd
  have hs : r^2/4 ≤ ‖x-x₀‖^2 := by nlinarith [norm_nonneg (x-x₀)]
  have ht : tangentPhase ψ x₀ x ≤ -r^2/4 := by
    change ψ x - ‖x-x₀‖^2 ≤ _
    linarith
  have ht0 : tangentPhase ψ x₀ x ≤ 0 := ht.trans (by nlinarith [sq_nonneg r])
  have hmul := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1+H*tangentPhase ψ x₀ x) ht0
  change tangentPhase ψ x₀ x + (H/2)*(tangentPhase ψ x₀ x*tangentPhase ψ x₀ x) ≤ _
  nlinarith only [ht, hmul]



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CoefficientEllipticFlux
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
open Set Filter Metric Manifold
open scoped Topology ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma coefficientElliptic_flux {ι : Type*} [Fintype ι] (e : ι → E)
    (a : ι → ι → SmoothScalar E) (u : SmoothScalar E) (x : E) :
    coefficientElliptic e a u x = ∑ i, fderiv ℝ
      (fun y => ∑ j, a i j y * SmoothScalar.directional (e j) u y) x (e i) := by
  have he : coefficientElliptic e a u =
      ∑ i, SmoothScalar.directional (e i) (∑ j, a i j * SmoothScalar.directional (e j) u) := by
    simp only [coefficientElliptic, map_sum]
  rw [he, SmoothScalar.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change fderiv ℝ _ x (e i) = _
  congr 2
  funext y
  simp only [SmoothScalar.sum_apply, Subalgebra.coe_mul, Pi.mul_apply]

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SphericalBaseProfileRadius
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma metricInverse_posDef (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) : ((metricCoefficients g p y)⁻¹).PosDef :=
  (metricCoefficients_posDef g p hy).inv


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
open Set Filter Manifold BoxIntegral
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_TestAsSmooth
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

lemma testAsSmooth_derivative (v : E) (u : EllipticTest K) :
    testAsSmooth K (testDerivative K v u) = SmoothScalar.directional v (testAsSmooth K u) := rfl
lemma testAsSmooth_multiply (b : SmoothScalar E) (u : EllipticTest K) :
    testAsSmooth K (testMultiply K b u) = b * testAsSmooth K u := by
  apply Subtype.ext; ext x; simp only [testAsSmooth_apply, testMultiply_apply, Subalgebra.coe_mul, Pi.mul_apply]
lemma testAsSmooth_sum {η : Type*} (s : Finset η) (u : η → EllipticTest K) :
    testAsSmooth K (∑ i ∈ s, u i) = ∑ i ∈ s, testAsSmooth K (u i) := by
  apply Subtype.ext
  ext x
  simp only [testAsSmooth_apply, SmoothScalar.sum_apply, FunLike.coe_sum, Finset.sum_apply]
lemma testAsSmooth_add (u v : EllipticTest K) :
    testAsSmooth K (u+v) = testAsSmooth K u + testAsSmooth K v := rfl

lemma SmoothScalar.eventuallyEq_directional (v : E) (u w : SmoothScalar E) (x : E)
    (h : (u : E → ℝ) =ᶠ[𝓝 x] w) :
    (SmoothScalar.directional v u : E → ℝ) =ᶠ[𝓝 x] SmoothScalar.directional v w := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  change fderiv ℝ (u : E → ℝ) y v = fderiv ℝ (w : E → ℝ) y v
  rw [hy]

lemma coefficientElliptic_eq_of_eventuallyEq (a : ι → ι → SmoothScalar E)
    (u w : SmoothScalar E) (x : E) (h : (u : E → ℝ) =ᶠ[𝓝 x] w) :
    coefficientElliptic e a u x = coefficientElliptic e a w x := by
  simp only [coefficientElliptic, SmoothScalar.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun f : E →L[ℝ] ℝ => f (e i))
    (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) ?_)
  filter_upwards [SmoothScalar.eventuallyEq_directional (e j) u w x h] with y hy
  change a i j y * SmoothScalar.directional (e j) u y = a i j y * SmoothScalar.directional (e j) w y
  rw [hy]

lemma coefficientSchrodinger_eq_of_eventuallyEq (a : ι → ι → SmoothScalar E) (V u w : SmoothScalar E)
    (x : E) (h : (u : E → ℝ) =ᶠ[𝓝 x] w) :
    coefficientSchrodinger e a V u x = coefficientSchrodinger e a V w x := by
  simp only [coefficientSchrodinger, Subalgebra.coe_add, Subalgebra.coe_mul, Pi.add_apply, Pi.mul_apply,
    coefficientElliptic_eq_of_eventuallyEq e a u w x h, h.eq_of_nhds]

lemma testSchrodinger_asSmooth (a : ι → ι → SmoothScalar E) (V : SmoothScalar E) (u : EllipticTest K) :
    testAsSmooth K (testSchrodinger K e a V u) = coefficientSchrodinger e a V (testAsSmooth K u) := by
  simp only [testSchrodinger, testElliptic, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    testAsSmooth_add, testAsSmooth_sum, testAsSmooth_derivative, testAsSmooth_multiply,
    coefficientElliptic, coefficientSchrodinger]

lemma testSchrodinger_eval_congr (a : ι → ι → SmoothScalar E) (V w : SmoothScalar E)
    (u : EllipticTest K) (x : E) (h : (u : E → ℝ) =ᶠ[𝓝 x] w) :
    testSchrodinger K e a V u x = coefficientSchrodinger e a V w x := by
  change testAsSmooth K (testSchrodinger K e a V u) x = _
  rw [testSchrodinger_asSmooth]
  exact coefficientSchrodinger_eq_of_eventuallyEq e a V (testAsSmooth K u) w x h

lemma testSchrodinger_zero_of_eventually_zero (a : ι → ι → SmoothScalar E) (V : SmoothScalar E)
    (u : EllipticTest K) (x : E) (h : (u : E → ℝ) =ᶠ[𝓝 x] 0) : testSchrodinger K e a V u x = 0 := by
  rw [testSchrodinger_eval_congr K e a V 0 u x h]
  simp [coefficientSchrodinger, coefficientElliptic]

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
section ScalarComposition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma scalar_comp_directional {F : ℝ → ℝ} {u : E → ℝ} {x : E}
    (hF : DifferentiableAt ℝ F (u x)) (hu : DifferentiableAt ℝ u x) (v : E) :
    fderiv ℝ (F ∘ u) x v = deriv F (u x) * fderiv ℝ u x v := by
  rw [fderiv_comp x hF hu, ContinuousLinearMap.comp_apply]
  exact fderiv_eq_deriv_mul
lemma scalar_comp_second_directional {F : ℝ → ℝ} {u : E → ℝ} {x : E}
    (hF : ContDiffAt ℝ 2 F (u x)) (hu : ContDiffAt ℝ 2 u x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (F ∘ u) y b) x a =
      deriv (deriv F) (u x) * fderiv ℝ u x a * fderiv ℝ u x b +
      deriv F (u x) * fderiv ℝ (fun y => fderiv ℝ u y b) x a := by
  have hdu := hu.differentiableAt (by norm_num)
  have hF' : DifferentiableAt ℝ (deriv F) (u x) :=
    by
      simpa only [fderiv_apply_one_eq_deriv] using
        ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
          (differentiableAt_const (1 : ℝ))
  have hdu' : DifferentiableAt ℝ (fun y => fderiv ℝ u y b) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have he : (fun y => fderiv ℝ (F ∘ u) y b) =ᶠ[𝓝 x]
      (fun y => deriv F (u y) * fderiv ℝ u y b) := by
    filter_upwards [hu.eventually (by norm_num),
      (hdu.continuousAt.preimage_mem_nhds (hF.eventually (by norm_num)))] with y hy hFy
    change ContDiffAt ℝ 2 F (u y) at hFy
    exact scalar_comp_directional (hFy.differentiableAt (by norm_num))
      (hy.differentiableAt (by norm_num)) b
  rw [he.fderiv_eq]
  erw [fderiv_fun_mul (hF'.comp x hdu) hdu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  have hfder := scalar_comp_directional hF' hdu a
  change fderiv ℝ (deriv F ∘ u) x a = _ at hfder
  rw [hfder]
  simp only [Function.comp_apply]
  ring
end ScalarComposition
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
lemma localLaplacian_expansion_at {u : M → ℝ}
    (g : SmoothMetric E M) (p : M) {y : E} (hy : y ∈ (chartAt E p).target)
    (hu : ContDiffAt ℝ 2 (u ∘ (chartAt E p).symm) y) :
    localLaplacian g u p y =
      (∑ i, ∑ j, (metricCoefficients g p y)⁻¹ i j *
        fderiv ℝ (fun z => fderiv ℝ (u ∘ (chartAt E p).symm) z (Module.finBasis ℝ E j)) y
          (Module.finBasis ℝ E i)) +
      ∑ j, metricFirstCoefficient g p j y *
        fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j) := by
  classical
  let ρ := fun z => Real.sqrt (metricCoefficients g p z).det
  let A := metricCoefficients g p
  let v := u ∘ (chartAt E p).symm
  let b := Module.finBasis ℝ E
  have hρ : DifferentiableAt ℝ ρ y := ((contDiffOn_metricDensity g p).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hA (i j : CoordIndex E) : DifferentiableAt ℝ (fun z => (A z)⁻¹ i j) y :=
    ((contDiffOn_metricInverse g p i j).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hv : DifferentiableAt ℝ (fderiv ℝ v) y :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he (i : CoordIndex E) : (fun z => metricFlux g u p z i) =
      fun z => ∑ j, (ρ z * (A z)⁻¹ i j) * fderiv ℝ v z (b j) := by
    funext z
    simp only [metricFlux, ρ, A, v, b, Finset.mul_sum, mul_assoc]
  have hder (i : CoordIndex E) : fderiv ℝ (fun z => metricFlux g u p z i) y (b i) =
      ∑ j, ((ρ y * (A y)⁻¹ i j) * fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i) +
        fderiv ℝ v y (b j) * fderiv ℝ (fun z => ρ z * (A z)⁻¹ i j) y (b i)) := by
    rw [he]
    erw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j z => (ρ z * (A z)⁻¹ i j) * fderiv ℝ v z (b j))
      (fun j _ => (hρ.mul (hA i j)).mul (hv.clm_apply (differentiableAt_const _)))]
    simp only [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    erw [fderiv_mul (c := fun z => ρ z * (A z)⁻¹ i j)
      (d := fun z => fderiv ℝ v z (b j)) (hρ.mul (hA i j))
      (hv.clm_apply (differentiableAt_const _))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  change (ρ y)⁻¹ * ∑ i, fderiv ℝ (fun z => metricFlux g u p z i) y (b i) = _
  simp_rw [hder, Finset.sum_add_distrib]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  have hn : ρ y ≠ 0 := (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  have hmain : (∑ i, (ρ y)⁻¹ * ∑ j, ρ y * (A y)⁻¹ i j *
      fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i)) =
      ∑ i, ∑ j, (A y)⁻¹ i j * fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [hmain]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [metricFirstCoefficient, ρ, A, b, v, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem laplaceBeltrami_comp_at {F : ℝ → ℝ} {u : M → ℝ}
    (g : SmoothMetric E M) (x : M) (hF : ContDiffAt ℝ 2 F (u x))
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u) :
    laplaceBeltrami g (F ∘ u) x = deriv F (u x) * laplaceBeltrami g u x +
      deriv (deriv F) (u x) * coordinateGradientPair g u u x := by
  let c := chartAt E x
  let b := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hF' : ContDiffAt ℝ 2 F ((u ∘ c.symm) (c x)) := by
    simpa only [Function.comp_apply,hinv] using hF
  have hFu : ContDiffAt ℝ 2 ((F ∘ u) ∘ c.symm) (c x) := hF'.comp (c x) hu'
  change localLaplacian g (F ∘ u) x (c x) =
    deriv F (u x) * localLaplacian g u x (c x) +
      deriv (deriv F) (u x) * coordinateGradientPair g u u x
  rw [localLaplacian_expansion_at g x hx hFu, localLaplacian_expansion_C2 hu g x hx]
  have hd1 (i : CoordIndex E) :
      fderiv ℝ ((F ∘ u) ∘ c.symm) (c x) (b i) =
      deriv F (u x) * fderiv ℝ (u ∘ c.symm) (c x) (b i) := by
    change fderiv ℝ (F ∘ (u ∘ c.symm)) (c x) (b i) = _
    rw [scalar_comp_directional (hF'.differentiableAt (by norm_num))
      (hu'.differentiableAt (by norm_num)), Function.comp_apply, hinv]
  have hd2 (i j : CoordIndex E) :
      fderiv ℝ (fun z => fderiv ℝ ((F ∘ u) ∘ c.symm) z (b j)) (c x) (b i) =
      deriv (deriv F) (u x) * fderiv ℝ (u ∘ c.symm) (c x) (b i) *
        fderiv ℝ (u ∘ c.symm) (c x) (b j) +
      deriv F (u x) * fderiv ℝ (fun z => fderiv ℝ (u ∘ c.symm) z (b j)) (c x) (b i) := by
    change fderiv ℝ (fun z => fderiv ℝ (F ∘ (u ∘ c.symm)) z (b j)) (c x) (b i) = _
    rw [scalar_comp_second_directional hF' hu', Function.comp_apply,hinv]
  change (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (fun z => fderiv ℝ ((F ∘ u) ∘ c.symm) z (b j)) (c x) (b i)) +
      ∑ j, metricFirstCoefficient g x j (c x) * fderiv ℝ ((F ∘ u) ∘ c.symm) (c x) (b j) = _
  simp_rw [hd1,hd2,mul_add,Finset.sum_add_distrib]
  unfold coordinateGradientPair
  simp only [Finset.mul_sum]
  simp only [mul_left_comm,mul_comm]
  ring



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


end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_DirectionalCompEquiv
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
open Set Filter Metric Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] (L : E ≃L[ℝ] F)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma directional_comp_equiv {f : E → ℝ} {y : F}
    (hf : DifferentiableAt ℝ f (L.symm y)) (v : E) :
    fderiv ℝ (f ∘ L.symm) y (L v) = fderiv ℝ f (L.symm y) v := by
  rw [fderiv_comp y hf L.symm.differentiableAt]
  simp only [L.symm.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    L.symm_apply_apply]

omit [FiniteDimensional ℝ F] in
lemma coefficientSchrodinger_metric_equiv (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ) (p : M) (y : F)
    (hy : L.symm y ∈ (chartAt E p).target)
    (a : CoordIndex E → CoordIndex E → SmoothScalar F) (V w : SmoothScalar F)
    (ha : ∀ᶠ z in 𝓝 y, ∀ i j,
      a i j z = Real.sqrt (metricCoefficients g p (L.symm z)).det *
        (metricCoefficients g p (L.symm z))⁻¹ i j)
    (hV : V y = lam * Real.sqrt (metricCoefficients g p (L.symm y)).det)
    (hw : (w : F → ℝ) =ᶠ[𝓝 y] (u ∘ (chartAt E p).symm) ∘ L.symm)
    (hsol : -laplaceBeltrami g u ((chartAt E p).symm (L.symm y)) =
      lam*u ((chartAt E p).symm (L.symm y))) :
    coefficientSchrodinger (fun i => L (Module.finBasis ℝ E i)) a V w y = 0 := by
  have hnh : ∀ᶠ z in 𝓝 y, L.symm z ∈ (chartAt E p).target :=
    L.symm.continuous.continuousAt.preimage_mem_nhds ((chartAt E p).open_target.mem_nhds hy)
  have he (i : CoordIndex E) :
      (fun z => ∑ j, a i j z * SmoothScalar.directional (L (Module.finBasis ℝ E j)) w z) =ᶠ[𝓝 y]
        (fun z => metricFlux g u p (L.symm z) i) := by
    filter_upwards [ha, hw.fderiv (𝕜 := ℝ),hnh] with z hza hzw hzt
    simp only [metricFlux, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [SmoothScalar.directional_apply,hzw,directional_comp_equiv L
      ((contDiffAt_inChart hu p hzt).differentiableAt (by simp))]
    rw [hza]; ring
  have heL : coefficientElliptic (fun i => L (Module.finBasis ℝ E i)) a w y =
      Real.sqrt (metricCoefficients g p (L.symm y)).det * localLaplacian g u p (L.symm y) := by
    rw [coefficientElliptic_flux]
    simp only [(he _).fderiv_eq]
    have hdiff (i : CoordIndex E) : DifferentiableAt ℝ (fun z => metricFlux g u p z i) (L.symm y) :=
      (differentiableAt_pi.mp (differentiableAt_metricFlux hu g p hy)) i
    simp only [show ∀ i, fderiv ℝ (fun z => metricFlux g u p (L.symm z) i) y
        (L (Module.finBasis ℝ E i)) = fderiv ℝ (fun z => metricFlux g u p z i) (L.symm y)
          (Module.finBasis ℝ E i) from fun i => directional_comp_equiv L (hdiff i) _]
    rw [localLaplacian, ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr
      (metricCoefficients_det_pos g p hy)).ne', one_mul]
  rw [laplaceBeltrami_inChart hu g p _ ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy] at hsol
  change coefficientElliptic (fun i => L (Module.finBasis ℝ E i)) a w y + V y*w y = 0
  rw [heL, hV, hw.eq_of_nhds]
  dsimp only [Function.comp_apply]
  have hh := congrArg (fun t : ℝ => Real.sqrt (metricCoefficients g p (L.symm y)).det * t) hsol
  nlinarith only [hh]

theorem exists_metric_ucp_model_equiv (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ)
    (hsol : ∀ x, -laplaceBeltrami g u x = lam*u x) (p : M) :
    ∃ (a : CoordIndex E → CoordIndex E → SmoothScalar F) (V w : SmoothScalar F) (r : ℝ),
      0 < r ∧ (∀ i j, a i j = a j i) ∧
      ball (L ((chartAt E p) p)) r ⊆ L.symm ⁻¹' (chartAt E p).target ∧
      (∀ y ∈ ball (L ((chartAt E p) p)) r, w y = u ((chartAt E p).symm (L.symm y))) ∧
      (∀ y ∈ ball (L ((chartAt E p) p)) r, Matrix.PosDef (fun i j => a i j y)) ∧
      (∀ y ∈ ball (L ((chartAt E p) p)) r,
        coefficientSchrodinger (fun i => L (Module.finBasis ℝ E i)) a V w y = 0) := by
  classical
  let ρ : F → ℝ := fun y => Real.sqrt (metricCoefficients g p (L.symm y)).det
  let G₀ : F → Matrix (CoordIndex E) (CoordIndex E) ℝ × (ℝ × ℝ) :=
    fun y => ((fun i j => ρ y * (metricCoefficients g p (L.symm y))⁻¹ i j),
      (lam*ρ y,u ((chartAt E p).symm (L.symm y))))
  let O := L.symm ⁻¹' (chartAt E p).target
  have hρ : ContDiffOn ℝ ∞ ρ O := (contDiffOn_metricDensity g p).comp
    L.symm.contDiff.contDiffOn (fun _ h => h)
  have hF : ContDiffOn ℝ ∞ G₀ O := by
    apply ContDiffOn.prodMk
    · exact contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j =>
        hρ.mul ((contDiffOn_metricInverse g p i j).comp L.symm.contDiff.contDiffOn (fun _ h => h))))
    · apply ContDiffOn.prodMk
      · exact contDiffOn_const.mul hρ
      · intro y hy
        exact ((contDiffAt_inChart hu p hy).comp y L.symm.contDiff.contDiffAt).contDiffWithinAt
  have hp : L ((chartAt E p) p) ∈ O := by
    simpa only [O, mem_preimage, L.symm_apply_apply] using
      (chartAt E p).map_source (mem_chart_source E p)
  have hO : IsOpen O := (chartAt E p).open_target.preimage L.symm.continuous
  obtain ⟨G,hG,he⟩ := smooth_extension_near_compact isCompact_singleton hO
    (singleton_subset_iff.mpr hp) hF
  have he' : G₀ =ᶠ[𝓝 (L ((chartAt E p) p))] G := he.filter_mono (nhds_le_nhdsSet (mem_singleton _))
  let a : CoordIndex E → CoordIndex E → SmoothScalar F := fun i j =>
    ⟨fun y => ((G y).1 i j + (G y).1 j i)/2, by
      change ContDiff ℝ ∞ (fun y => ((G y).1 i j + (G y).1 j i)/2)
      exact ((contDiff_pi.mp (contDiff_pi.mp hG.fst i) j).add
        (contDiff_pi.mp (contDiff_pi.mp hG.fst j) i)).div_const 2⟩
  let V : SmoothScalar F := ⟨fun y => (G y).2.1,hG.snd.fst⟩
  let w : SmoothScalar F := ⟨fun y => (G y).2.2,hG.snd.snd⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.eventually_nhds_iff.mp (he'.and (hO.mem_nhds hp))
  have heq (y : F) (hy : y ∈ ball (L ((chartAt E p) p)) r) :
      (∀ i j, a i j y = ρ y*(metricCoefficients g p (L.symm y))⁻¹ i j) ∧
        V y = lam*ρ y ∧ w y = u ((chartAt E p).symm (L.symm y)) := by
    have hny := hrsub hy
    have hsym (i j : CoordIndex E) : (metricCoefficients g p (L.symm y))⁻¹ j i =
        (metricCoefficients g p (L.symm y))⁻¹ i j := by
      have hh := congrArg (fun B : Matrix (CoordIndex E) (CoordIndex E) ℝ => B i j)
        (metricInverse_posDef g p hny.2).isHermitian
      simpa only [Matrix.conjTranspose_apply, star_trivial] using hh
    have hg : G y = G₀ y := hny.1.symm
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · change ((G y).1 i j+(G y).1 j i)/2 = _
      rw [hg]; dsimp only [G₀]; rw [hsym]; ring
    · change (G y).2.1 = _
      rw [hg]
    · change (G y).2.2 = _
      rw [hg]
  refine ⟨a,V,w,r,hr,?_,fun y hy => (hrsub hy).2,
    fun y hy => (heq y hy).2.2,?_,?_⟩
  · intro i j
    apply Subtype.ext; ext y
    change (_+_)/2 = (_+_)/2
    rw [add_comm]
  · intro y hy
    simp only [(heq y hy).1]
    exact (metricInverse_posDef g p (hrsub hy).2).smul (Real.sqrt_pos.mpr
      (metricCoefficients_det_pos g p (hrsub hy).2))
  · intro y hy
    apply coefficientSchrodinger_metric_equiv L g hu lam p y (hrsub hy).2 a V w
    · filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      exact (heq z hz).1
    · exact (heq y hy).2.1
    · filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      exact (heq z hz).2.2
    · exact hsol _
end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_LocalZeroAcrossLevel
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E)

lemma exponential_square_integrable (φ : SmoothScalar E) (τ : ℝ) (u : EllipticTest K) :
    Integrable (fun x => Real.exp (2*τ*φ x)*(u x*u x)) (volume : Measure E) := by
  convert testPair_integrable K (testMultiply K (exponentialWeight φ τ) u)
    (testMultiply K (exponentialWeight φ τ) u) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [testMultiply_apply, exponentialWeight_apply]
  rw [show 2*τ*φ x = τ*φ x+τ*φ x by ring, Real.exp_add]
  ring

lemma exponential_square_integral (φ : SmoothScalar E) (τ : ℝ) (u : EllipticTest K) :
    testPair K (testMultiply K (exponentialWeight φ τ) u)
      (testMultiply K (exponentialWeight φ τ) u) =
      ∫ x, Real.exp (2*τ*φ x)*(u x*u x) := by
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [testMultiply_apply, exponentialWeight_apply]
  rw [show 2*τ*φ x = τ*φ x+τ*φ x by ring, Real.exp_add]
  ring

lemma exponential_square_lower (φ : SmoothScalar E) (τ b : ℝ) (hτ : 0 ≤ τ)
    (u : EllipticTest K) :
    Real.exp (2*τ*b) * (∫ x in {x | b < φ x}, u x*u x) ≤
      testPair K (testMultiply K (exponentialWeight φ τ) u)
        (testMultiply K (exponentialWeight φ τ) u) := by
  have hS : MeasurableSet {x | b < φ x} :=
    isOpen_lt continuous_const (SmoothScalar.contDiff φ).continuous |>.measurableSet
  rw [exponential_square_integral, ← integral_indicator hS, ← integral_const_mul]
  apply integral_mono (((testPair_integrable K u u).indicator hS).const_mul _)
    (exponential_square_integrable K φ τ u)
  intro x
  dsimp only
  by_cases hx : b < φ x
  · rw [indicator_of_mem (show x ∈ {y : E | b < φ y} from hx)]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.le (by positivity))) (mul_self_nonneg _)
  · rw [indicator_of_notMem (show x ∉ {y : E | b < φ y} from hx), mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (mul_self_nonneg _)

lemma exponential_square_upper (φ : SmoothScalar E) (τ c : ℝ) (hτ : 0 ≤ τ)
    (r : EllipticTest K) (hr : ∀ x, c < φ x → r x = 0) :
    testPair K (testMultiply K (exponentialWeight φ τ) r)
        (testMultiply K (exponentialWeight φ τ) r) ≤
      Real.exp (2*τ*c) * testPair K r r := by
  rw [exponential_square_integral, testPair, ← integral_const_mul]
  apply integral_mono (exponential_square_integrable K φ τ r)
    ((testPair_integrable K r r).const_mul _)
  intro x
  by_cases hx : c < φ x
  · simp only [hr x hx, mul_zero, le_refl]
  · exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_not_gt hx) (by positivity)))
      (mul_self_nonneg _)

theorem exponential_support_dominance (φ : SmoothScalar E) (u r : EllipticTest K)
    (C T c : ℝ) (hC : 0 ≤ C)
    (hest : ∀ τ ≥ T,
      testPair K (testMultiply K (exponentialWeight φ τ) u) (testMultiply K (exponentialWeight φ τ) u) ≤
        C * testPair K (testMultiply K (exponentialWeight φ τ) r) (testMultiply K (exponentialWeight φ τ) r))
    (hr : ∀ x, c < φ x → r x = 0) : ∀ x, c < φ x → u x = 0 := by
  intro x hx
  obtain ⟨b,hcb,hbx⟩ := exists_between hx
  let S := {y | b < φ y}
  let J := ∫ y in S, u y*u y
  have hJ : 0 ≤ J := integral_nonneg fun _ => mul_self_nonneg _
  have hbound : ∀ᶠ τ : ℝ in atTop, J ≤
      C * testPair K r r * Real.exp ((2*(c-b))*τ) := by
    filter_upwards [eventually_ge_atTop (max T 0)] with τ hτ
    have ht := (le_max_left ..).trans hτ
    have ht0 := (le_max_right ..).trans hτ
    have hlo := exponential_square_lower K φ τ b ht0 u
    have hup := exponential_square_upper K φ τ c ht0 r hr
    have hh := hlo.trans ((hest τ ht).trans (mul_le_mul_of_nonneg_left hup hC))
    change Real.exp (2*τ*b)*J ≤ C*(Real.exp (2*τ*c)*testPair K r r) at hh
    apply (mul_le_mul_iff_right₀ (Real.exp_pos (2*τ*b))).mp
    refine hh.trans_eq ?_
    rw [show Real.exp (2*τ*c) = Real.exp (2*τ*b)*Real.exp ((2*(c-b))*τ) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  have hlim : Tendsto (fun τ : ℝ => C*testPair K r r*Real.exp ((2*(c-b))*τ)) atTop (𝓝 0) := by
    have he : Tendsto (fun τ : ℝ => Real.exp ((2*(c-b))*τ)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (by linarith : 2*(c-b) < 0)).mpr tendsto_id)
    simpa only [mul_zero] using he.const_mul (C*testPair K r r)
  have hJ0 : J = 0 := le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound) hJ
  have hae : (fun y => u y*u y) =ᵐ[(volume : Measure E).restrict S] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => mul_self_nonneg _) (testPair_integrable K u u).restrict).mp hJ0
  have hop : IsOpen S := isOpen_lt continuous_const (SmoothScalar.contDiff φ).continuous
  have heq := (volume : Measure E).eqOn_open_of_ae_eq hae hop (u.contDiff.continuous.mul u.contDiff.continuous).continuousOn
    continuous_const.continuousOn
  have hh := heq hbx
  simpa using (mul_self_eq_zero.mp hh)


end

open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] (e : ι → E)

theorem local_zero_across_level (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (V ψ u : SmoothScalar E) (x₀ : E)
    (hψ : ψ x₀ = 0) (hpos : Matrix.PosDef (fun i j => a i j x₀))
    (hgrad : (fun i => SmoothScalar.directional (e i) ψ x₀) ≠ 0)
    (O : Set E) (hO : IsOpen O) (hx₀ : x₀ ∈ O)
    (hsol : ∀ x ∈ O, coefficientSchrodinger e a V u x = 0)
    (hzero : ∀ x ∈ O, 0 < ψ x → u x = 0) : (u : E → ℝ) =ᶠ[𝓝 x₀] 0 := by
  let η := tangentPhase ψ x₀
  have hη : η x₀ = 0 := tangentPhase_at ψ x₀ hψ
  have hηgrad : (fun i => SmoothScalar.directional (e i) η x₀) ≠ 0 := by
    simpa only [η, tangentPhase_derivative_center] using hgrad
  obtain ⟨H,hH,U,hU,T,_hT,hcar⟩ := exists_local_weighted_carleman e a ha V η x₀ hη hpos hηgrad
  let φ := convexifyPhase η H
  have hφ₀ : φ x₀ = 0 := by
    change η x₀ + (H/2)*(η x₀*η x₀) = 0
    rw [hη]; ring
  have hsmall : ∀ᶠ x in 𝓝 x₀, -1 < H*η x :=
    ((((continuous_const.mul (SmoothScalar.contDiff η).continuous) :
      Continuous (fun x => H*η x)).tendsto x₀).eventually_const_lt (by change -1 < H*η x₀; rw [hη]; norm_num))
  obtain ⟨R,hR,hRsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hU (inter_mem (hO.mem_nhds hx₀) hsmall))
  let r := R/2
  have hr : 0 < r := half_pos hR
  let K : Compacts E := ⟨Metric.closedBall x₀ r, isCompact_closedBall x₀ r⟩
  have hK (x : E) (hx : x ∈ K) : x ∈ U ∧ x ∈ O ∧ -1 < H*η x := by
    apply hRsub
    apply lt_of_le_of_lt (show dist x x₀ ≤ r from hx)
    dsimp [r]; linarith
  let χ : ContDiffBump x₀ := ⟨r/2,r, half_pos hr, by linarith⟩
  let w : EllipticTest K := ⟨fun x => χ x * u x, χ.contDiff.mul (SmoothScalar.contDiff u), by
    intro x hx
    have hχ : χ x = 0 := χ.zero_of_le_dist (by
      change ¬ dist x x₀ ≤ r at hx
      exact (lt_of_not_ge hx).le)
    simp only [hχ, zero_mul, Pi.zero_apply]⟩
  have hw (x : E) : w x = χ x * u x := rfl
  let c := -r^2/8
  have hc : c < 0 := by dsimp [c]; nlinarith [sq_pos_of_pos hr]
  have hres : ∀ x, c < φ x → testSchrodinger K e a V w x = 0 := by
    intro x hxphi
    by_cases hxK : x ∈ K
    · have hxO := (hK x hxK).2.1
      by_cases hxi : x ∈ Metric.ball x₀ (r/2)
      · have heq : (w : E → ℝ) =ᶠ[𝓝 x] u := by
          filter_upwards [χ.eventuallyEq_one_of_mem_ball hxi] with y hy
          simp only [hw, Pi.one_apply] at *
          rw [hy, one_mul]
        rw [testSchrodinger_eval_congr K e a V u w x heq]
        exact hsol x hxO
      · have hxψ : 0 < ψ x := by
          by_contra hn
          have hgap := tangentPhase_annular_gap ψ x₀ x r H hr (le_of_not_gt hn)
            (le_of_not_gt hxi) (hK x hxK).2.2
          change φ x ≤ c at hgap
          exact not_lt_of_ge hgap hxphi
        have heq : (w : E → ℝ) =ᶠ[𝓝 x] 0 := by
          filter_upwards [hO.mem_nhds hxO,
            (isOpen_lt continuous_const (SmoothScalar.contDiff ψ).continuous).mem_nhds hxψ] with y hyO hyψ
          simp only [hw, hzero y hyO hyψ, mul_zero, Pi.zero_apply]
        exact testSchrodinger_zero_of_eventually_zero K e a V w x heq
    · exact (testSchrodinger K e a V w).zero_on_compl hxK
  have hupper := exponential_support_dominance K φ w (testSchrodinger K e a V w) 8 T c
    (by norm_num) (fun τ hτ => hcar K (fun x hx => (hK x hx).1) τ hτ w) hres
  filter_upwards [(isOpen_lt continuous_const (SmoothScalar.contDiff φ).continuous).mem_nhds
    (show c < φ x₀ by rw [hφ₀]; exact hc), Metric.ball_mem_nhds x₀ (half_pos hr)] with x hxφ hxb
  have hχ : χ x = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hxb)
  have hh := hupper x hxφ
  simpa only [hw, hχ, one_mul, Pi.zero_apply] using hh



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ZeroInterior
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
open MeasureTheory TopologicalSpace Filter Set Metric
open scoped Distributions ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma zeroInterior_open (u : SmoothScalar E) : IsOpen (zeroInterior u) :=
  isOpen_setOfPred_eventually_nhds
lemma zero_of_mem_zeroInterior (u : SmoothScalar E) {x : E} (hx : x ∈ zeroInterior u) : u x = 0 :=
  hx.eq_of_nhds

lemma ballPhase_positive_iff (y x : E) (r : ℝ) (hr : 0 < r) :
    0 < ballPhase y r x ↔ x ∈ ball y r := by
  rw [ballPhase_apply, mem_ball, dist_eq_norm]
  constructor <;> intro h <;> nlinarith [norm_nonneg (x-y)]
lemma ballPhase_zero_of_dist (y x : E) (r : ℝ) (h : dist x y = r) : ballPhase y r x = 0 := by
  rw [ballPhase_apply, ← dist_eq_norm, h, sub_self]
lemma distanceSquare_directional (y x v : E) :
    SmoothScalar.directional v (distanceSquare y) x = 2*⟪x-y,v⟫ := by
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const y).norm_sq
  simp only [id_eq] at hd
  change fderiv ℝ (fun x : E => ‖x-y‖^2) x v = _
  rw [hd.fderiv]
  simp [inner_sub_left]
lemma ballPhase_directional (y x v : E) (r : ℝ) :
    SmoothScalar.directional v (ballPhase y r) x = -2*⟪x-y,v⟫ := by
  rw [ballPhase, map_sub]
  change SmoothScalar.directional v (algebraMap ℝ (SmoothScalar E) (r^2)) x -
    SmoothScalar.directional v (distanceSquare y) x = _
  rw [distanceSquare_directional]
  have hc : SmoothScalar.directional v (algebraMap ℝ (SmoothScalar E) (r^2)) x = 0 := by
    change fderiv ℝ (fun _ : E => r^2) x v = 0
    rw [fderiv_const_apply, _root_.zero_apply]
  rw [hc]; ring
omit [Fintype ι] in
lemma ballPhase_gradient_ne_zero (e : Module.Basis ι ℝ E) (y x : E) (r : ℝ)
    (hxy : x ≠ y) : (fun i => SmoothScalar.directional (e i) (ballPhase y r) x) ≠ 0 := by
  intro h
  have hf : (innerSL ℝ (x-y)).toLinearMap = 0 := by
    apply e.ext
    intro i
    change ⟪x-y,e i⟫ = 0
    have hi := congrFun h i
    rw [ballPhase_directional] at hi
    simp only [Pi.zero_apply] at hi
    linarith
  have hz : x-y = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp
    (congrArg (fun f : E →ₗ[ℝ] ℝ => f (x-y)) hf)
  exact hxy (sub_eq_zero.mp hz)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma zero_near_tangent_ball (e : Module.Basis ι ℝ E) (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (V u : SmoothScalar E)
    (O : Set E) (hO : IsOpen O) (y x : E) (r : ℝ) (hr : 0 < r)
    (hx : x ∈ O) (hxy : dist x y = r) (hpos : Matrix.PosDef (fun i j => a i j x))
    (hsol : ∀ z ∈ O, coefficientSchrodinger e a V u z = 0)
    (hz : ∀ z ∈ ball y r, u z = 0) : x ∈ zeroInterior u := by
  apply local_zero_across_level e a ha V (ballPhase y r) u x
    (ballPhase_zero_of_dist y x r hxy) hpos
    (ballPhase_gradient_ne_zero e y x r (by intro heq; simp [heq] at hxy; linarith)) O hO hx hsol
  intro z _ hzφ
  exact hz z ((ballPhase_positive_iff y z r hr).mp hzφ)

theorem weak_unique_continuation (e : Module.Basis ι ℝ E) (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (V u : SmoothScalar E)
    (O : Set E) (hO : IsOpen O) (hconn : IsPreconnected O)
    (hpos : ∀ x ∈ O, Matrix.PosDef (fun i j => a i j x))
    (hsol : ∀ x ∈ O, coefficientSchrodinger e a V u x = 0)
    (hz : (O ∩ zeroInterior u).Nonempty) : ∀ x ∈ O, u x = 0 := by
  have hclosed : closure (zeroInterior u) ∩ O ⊆ zeroInterior u := by
    intro x hx
    by_contra hxn
    obtain ⟨R,hR,hsub⟩ := Metric.isOpen_iff.mp hO x hx.2
    obtain ⟨y,hy,hyx⟩ := Metric.mem_closure_iff.mp hx.1 (R/4) (by positivity)
    have hne : (zeroInterior u)ᶜ.Nonempty := ⟨x,hxn⟩
    have hc := (zeroInterior_open u).isClosed_compl
    obtain ⟨z,hz,hzd⟩ := hc.exists_infDist_eq_dist hne y
    let r := infDist y (zeroInterior u)ᶜ
    have hr : 0 < r := hc.notMem_iff_infDist_pos hne |>.mp (by simpa using hy)
    have hrbound : r ≤ dist y x := infDist_le_dist_of_mem hxn
    have hzO : z ∈ O := by
      apply hsub
      change dist z x < R
      have ht := dist_triangle z y x
      rw [dist_comm z y, ← hzd] at ht
      rw [dist_comm x y] at hyx
      dsimp [r] at hrbound
      linarith
    have hball : ∀ w ∈ ball y r, u w = 0 := by
      intro w hw
      apply zero_of_mem_zeroInterior u
      by_contra hwn
      have dd : r ≤ dist y w := infDist_le_dist_of_mem hwn
      exact (lt_of_lt_of_le (by simpa only [mem_ball, dist_comm] using hw) dd).false
    have hznear := zero_near_tangent_ball e a ha V u O hO y z r hr hzO
      (by rw [dist_comm, ← hzd]) (hpos z hzO) hsol hball
    exact hz hznear
  have hsub := hconn.subset_of_closure_inter_subset (zeroInterior_open u) hz hclosed
  intro x hx
  exact zero_of_mem_zeroInterior u (hsub hx)

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
open Set Filter Metric Manifold
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem metric_unique_continuation_general [PreconnectedSpace M] (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ)
    (hsol : ∀ x, -laplaceBeltrami g u x = lam*u x)
    (hz : ∃ x, u =ᶠ[𝓝 x] 0) : u = 0 := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let L : E ≃L[ℝ] F := toEuclidean
  let Z := {x : M | u =ᶠ[𝓝 x] 0}
  have hZ : IsOpen Z := isOpen_setOfPred_eventually_nhds
  have hcl : closure Z ⊆ Z := by
    intro p hp
    obtain ⟨a,V,w,r,hr,ha,hT,hw,hpos,hP⟩ := exists_metric_ucp_model_equiv L g hu lam hsol p
    let c := chartAt E p
    have hps : p ∈ c.source := mem_chart_source E p
    have hb : ball (L (c p)) r ∈ 𝓝 (L (c p)) := ball_mem_nhds _ hr
    have hN : c.source ∩ (fun x => L (c x)) ⁻¹' ball (L (c p)) r ∈ 𝓝 p :=
      inter_mem (c.open_source.mem_nhds hps)
        ((L.continuous.continuousAt.comp (c.continuousAt hps)).preimage_mem_nhds hb)
    obtain ⟨x,hxN,hxZ⟩ := mem_closure_iff_nhds.mp hp _ hN
    have hct : c x ∈ c.target := c.map_source hxN.1
    have hctend : Tendsto (fun y => c.symm (L.symm y)) (𝓝 (L (c x))) (𝓝 x) := by
      have htL : Tendsto L.symm (𝓝 (L (c x))) (𝓝 (c x)) := by
        simpa only [L.symm_apply_apply] using L.symm.continuous.continuousAt.tendsto (x := L (c x))
      have ht := ((c.continuousAt_symm hct).tendsto).comp htL
      simpa only [L.symm_apply_apply,Function.comp_def,c.left_inv hxN.1] using ht
    have hzw : L (c x) ∈ zeroInterior w := by
      filter_upwards [isOpen_ball.mem_nhds hxN.2, hxZ.comp_tendsto hctend] with y hy hyz
      change w y = 0
      rw [hw y hy]
      exact hyz
    let e : Module.Basis (CoordIndex E) ℝ F := (Module.finBasis ℝ E).map L.toLinearEquiv
    have hwzero := weak_unique_continuation e a ha V w
      (ball (L (c p)) r) isOpen_ball (convex_ball (L (c p)) r).isPreconnected hpos hP
      ⟨L (c x),hxN.2,hzw⟩
    have hpzero : u =ᶠ[𝓝 p] 0 := by
      filter_upwards [hN] with x hx
      have hh := hwzero (L (c x)) hx.2
      rw [hw (L (c x)) hx.2,L.symm_apply_apply,c.left_inv hx.1] at hh
      exact hh
    exact hpzero
  have hsub : (univ : Set M) ⊆ Z := isPreconnected_univ.subset_of_closure_inter_subset hZ
    (by obtain ⟨x,hx⟩ := hz; exact ⟨x,mem_univ _,hx⟩) (fun _ hx => hcl hx.1)
  funext x
  exact (hsub (mem_univ x)).eq_of_nhds


end

open Set Filter Function Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma proportional_eigen_global_oai [PreconnectedSpace M] (g : SmoothMetric E M)
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (ell c : ℝ)
    (hue : ∀ x, -laplaceBeltrami g u x = ell*u x)
    (hve : ∀ x, -laplaceBeltrami g v x = ell*v x)
    (he : ∃ x, v =ᶠ[𝓝 x] (fun y => c*u y)) : v = fun y => c*u y := by
  have hcu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun y => c*u y) := contMDiff_const.mul hu
  let w := fun y => v y - c*u y
  have hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w := hv.sub (contMDiff_const.mul hu)
  have hscalar (x : M) : laplaceBeltrami g (fun y => c*u y) x = c * laplaceBeltrami g u x := by
    have hh := laplaceBeltrami_comp_at g x
      ((contDiff_const.mul contDiff_id : ContDiff ℝ 2 (fun s : ℝ => c*s)).contDiffAt) (hu.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    have hd : deriv (fun s : ℝ => c*s) = fun _ => c := by
      funext s; simp
    simpa only [Function.comp_def,hd,deriv_const,mul_zero,zero_mul,add_zero] using hh
  have hsub (x : M) : laplaceBeltrami g w x =
      laplaceBeltrami g v x - laplaceBeltrami g (fun y => c*u y) x := by
    have hh := congrArg Complex.re (complexLaplaceBeltrami_sub
      (Complex.ofRealCLM.contMDiff.comp (hv.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))))
      (Complex.ofRealCLM.contMDiff.comp (hcu.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))) g x)
    simpa only [complexLaplaceBeltrami,Complex.sub_re,Complex.add_re,Complex.mul_re,
      Complex.I_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero,
      Function.comp_def,Complex.ofRealCLM_apply,Pi.sub_apply,w] using hh
  have hwz : w = 0 := metric_unique_continuation_general g hw ell (fun x => by
    rw [hsub,hscalar]
    dsimp only [w]
    rw [show laplaceBeltrami g v x = -ell*v x by linarith [hve x],
      show laplaceBeltrami g u x = -ell*u x by linarith [hue x]]
    ring) (by
      obtain ⟨x,hx⟩ := he
      refine ⟨x,?_⟩
      filter_upwards [hx] with y hy
      simp only [w,hy,sub_self,Pi.zero_apply])
  funext x
  have hh := congrFun hwz x
  change v x - c*u x = 0 at hh
  exact sub_eq_zero.mp hh



end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.proportional_eigen_global_oai.{u_1, u_2} := @OAI.YauCounterexamples.proportional_eigen_global_oai.{u_1, u_2}
