-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_spherical_global_quasimodes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:30:46.80673+00:00
-- url     : https://prove2.me/submissions/73f71fef-c253-4239-84a6-eb96df922c72

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007
import Definitions.Def_OAIQ070A008
import Theorems.Thm_OAI_YauCounterexamples_exists_spherical_chart_quasimodes
import Theorems.Thm_OAI_YauCounterexamples_spherical_global_jet_lower
import Theorems.Thm_OAI_YauCounterexamples_spherical_wave_background_chart_bounds

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_LpInverseGramFstContraction
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
open Set Filter Function Module
open scoped Matrix InnerProductSpace
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq ι] in
lemma gram_mul_repr (b : Basis ι ℝ E) (u : E) :
    (Matrix.gram ℝ b) *ᵥ (fun i => b.repr u i) = fun i => inner ℝ (b i) u := by
  ext i
  calc
    _ = inner ℝ (b i) (∑ j, b.repr u j • b j) := by
      simp only [inner_sum,inner_smul_right,Matrix.mulVec,dotProduct,Matrix.gram_apply]
      simp only [mul_comm]
    _ = _ := by rw [b.sum_repr]

lemma inverse_gram_inner (b : Basis ι ℝ E) (u : E) :
    (Matrix.gram ℝ b)⁻¹ *ᵥ (fun i => inner ℝ (b i) u) = fun i => b.repr u i := by
  rw [← gram_mul_repr, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos.ne')]
  simp

theorem inverse_gram_contraction (b : Basis ι ℝ E) (u v : E) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b j) u * inner ℝ (b i) v =
      inner ℝ u v := by
  calc
    _ = ∑ i, b.repr u i * inner ℝ (b i) v := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul]
      have hh := congrFun (inverse_gram_inner b u) i
      change (∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b j) u) = b.repr u i at hh
      rw [hh]
    _ = inner ℝ (∑ i, b.repr u i • b i) v := by
      simp only [sum_inner,inner_smul_left,conj_trivial]
    _ = _ := by rw [b.sum_repr]


end

open Set Filter Function Module
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LinearPowerDirectional
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma roundChart_zero (p : E) (L : F →ₗᵢ[ℝ] E) : roundChart p L 0 = p := by
  simp [roundChart,stereoInvFunAux]

lemma roundChart_first (p : E) (L : F →ₗᵢ[ℝ] E) :
    HasFDerivAt (roundChart p L) L.toContinuousLinearMap 0 := by
  have h : HasFDerivAt (stereoInvFunAux (-p)) (ContinuousLinearMap.id ℝ E)
      (L.toContinuousLinearMap 0) := by simpa using hasFDerivAt_stereoInvFunAux (-p)
  convert h.comp (0:F) L.toContinuousLinearMap.hasFDerivAt using 1
  · rfl
  · ext z
    rfl


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
open Set Filter Function
open scoped ContDiff InnerProductSpace Topology




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
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace

variable {n : ℕ}

attribute [local instance] OAI.YauCounterexamples.instFactEqNatFinrankRealEuclideanHAddOfNat
lemma sphere_chart_symm (p : Sphere n) :
    (fun y => ((chartAt (Euclidean n) p).symm y : Euclidean (n+1))) =
      roundChart (p : Euclidean (n+1)) (sphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : Euclidean (n+1)) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,sphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

lemma sphere_chart_center (p : Sphere n) : chartAt (Euclidean n) p p = 0 := by
  have hh : (chartAt (Euclidean n) p).symm 0 = p := by
    apply Subtype.ext
    change (fun y => ((chartAt (Euclidean n) p).symm y : Euclidean (n+1))) 0 = _
    rw [sphere_chart_symm,roundChart_zero]
  have hz : (0 : Euclidean n) ∈ (chartAt (Euclidean n) p).target := by
    change 0 ∈ (stereographic' n (-p)).target
    simp
  exact (congrArg (chartAt (Euclidean n) p) hh).symm.trans ((chartAt (Euclidean n) p).right_inv hz)

lemma sphere_coordinate_embedding (p : Sphere n) (y : Euclidean n) (v : Euclidean n) :
    mfderiv 𝓘(ℝ,Euclidean n) 𝓘(ℝ,Euclidean (n+1))
      (fun q : Sphere n => (q : Euclidean (n+1))) ((chartAt (Euclidean n) p).symm y)
      (mfderiv 𝓘(ℝ,Euclidean n) 𝓘(ℝ,Euclidean n) (chartAt (Euclidean n) p).symm y v) =
        fderiv ℝ (roundChart (p : Euclidean (n+1)) (sphereFrame p)) y v := by
  have hy : y ∈ (chartAt (Euclidean n) p).target := by rw [sphere_chart_target]; trivial
  have hh := mfderiv_comp y
    ((contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp)).mdifferentiableAt
    ((contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (n := ∞) p) hy).mdifferentiableAt (by simp))
  have he := congrArg (fun L => L v) hh
  rw [mfderiv_eq_fderiv] at he
  rw [← sphere_chart_symm]
  exact he.symm


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
open Set Filter Manifold BoxIntegral Metric
open scoped Topology ContDiff InnerProductSpace

lemma sphericalRadius_nonneg (a b : Euclidean 4) (q : Sphere 3) :
    0 ≤ sphericalRadius a b q := Real.sqrt_nonneg _

lemma sphericalRadius_sq (a b : Euclidean 4) (q : Sphere 3) :
    (sphericalRadius a b q)^2 =
      (inner ℝ a (q : Euclidean 4))^2+(inner ℝ b (q : Euclidean 4))^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactExteriorBackgroundDomination
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
open scoped Topology ContDiff Manifold InnerProductSpace
namespace YauCounterexamples

theorem compact_exterior_background_domination {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {r φ : X → ℝ}
    (hr : ContinuousOn r K) (hφ : ContinuousOn φ K)
    (hrpos : ∀ x ∈ K, 0 < r x) (hgap : ∀ x ∈ K, φ x < Real.log (r x)) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ K, (n:ℝ)^k*Real.exp ((n:ℝ)*φ x) < (r x)^n := by
  classical
  by_cases hne : K.Nonempty
  · let f := fun x => Real.exp (φ x)/r x
    have hf : ContinuousOn f K := hφ.rexp.div hr (fun x hx => (hrpos x hx).ne')
    obtain ⟨z,hz,hm⟩ := hK.exists_isMaxOn hne hf
    have hfz : 0 < f z := div_pos (Real.exp_pos _) (hrpos z hz)
    have hlt : f z < 1 := by
      apply (div_lt_one (hrpos z hz)).mpr
      rw [←Real.exp_log (hrpos z hz)]
      exact Real.exp_lt_exp.mpr (hgap z hz)
    have ht := tendsto_pow_const_mul_const_pow_of_lt_one k hfz.le hlt
    filter_upwards [ht.eventually (Iio_mem_nhds zero_lt_one)] with n hn
    intro x hx
    have hfx : Real.exp (φ x) ≤ f z*r x := (div_le_iff₀ (hrpos x hx)).mp (hm hx)
    have hp := pow_le_pow_left₀ (Real.exp_pos (φ x)).le hfx n
    rw [←Real.exp_nat_mul,mul_pow] at hp
    calc
      _ ≤ (n:ℝ)^k*((f z)^n*(r x)^n) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = ((n:ℝ)^k*(f z)^n)*(r x)^n := by ring
      _ < 1*(r x)^n := mul_lt_mul_of_pos_right hn (pow_pos (hrpos x hx) n)
      _ = _ := one_mul _
  · exact Filter.Eventually.of_forall (fun n x hx => (hne ⟨x,hx⟩).elim)
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RoundMetricExists
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
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma localGradientPair_eq_global {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    localGradientPair g u u p y = coordinateGradientPair g u u ((chartAt E p).symm y) := by
  rw [coordinateGradientPair_inChart hu hu g p ((chartAt E p).symm y) ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy]


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartGradientProjectionSmooth
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
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_nonneg (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    0 ≤ coordinateGradientPair g u u x := by
  have hp := (metricCoefficients_posDef g x
    ((chartAt E x).map_source (mem_chart_source E x))).inv.posSemidef.dotProduct_mulVec_nonneg
    (fun i => fderiv ℝ (u ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E i))
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at hp
  convert hp using 1; try rfl
  unfold coordinateGradientPair
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring


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
open scoped Topology ContDiff Manifold Matrix


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_AnnularRelativeMargin
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}
lemma round_metricCoefficients_at (g : SmoothMetric (Euclidean d) (Sphere d)) (p : Sphere d)
    (hg : ∀ (v w : TangentSpace 𝓘(ℝ,Euclidean d) p),
      g.inner p v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p w)) :
    metricCoefficients g p 0 = Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)) := by
  have hp : (chartAt (Euclidean d) p).symm 0 = p := by
    simpa only [sphere_chart_center] using (chartAt (Euclidean d) p).left_inv (mem_chart_source _ p)
  have hg' : ∀ (v w : TangentSpace 𝓘(ℝ,Euclidean d) ((chartAt (Euclidean d) p).symm 0)),
      g.inner ((chartAt (Euclidean d) p).symm 0) v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) ((chartAt (Euclidean d) p).symm 0) v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) ((chartAt (Euclidean d) p).symm 0) w) := by
    change (fun q : Sphere d => ∀ v w : TangentSpace 𝓘(ℝ,Euclidean d) q,
      g.inner q v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) q v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) q w))
      ((chartAt (Euclidean d) p).symm 0)
    rw [hp]
    exact hg
  let : ContinuousSMul ℝ (Euclidean d) := IsBoundedSMul.continuousSMul
  let : ContinuousSMul ℝ (Euclidean (d+1)) := IsBoundedSMul.continuousSMul
  have hround : fderiv ℝ (roundChart (p : Euclidean (d+1)) (sphereFrame p)) 0 =
      (sphereFrame p).toContinuousLinearMap :=
    (roundChart_first (p : Euclidean (d+1)) (sphereFrame p)).fderiv
  ext i j
  rw [metricCoefficients,hg']
  rw [coordinateVector,coordinateVector,sphere_coordinate_embedding p 0,
    sphere_coordinate_embedding p 0,hround]
  exact (sphereFrame p).inner_map_map _ _



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

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CutoffFactorCompactRaw
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open Set Filter Manifold
open scoped Topology ContDiff InnerProductSpace

lemma inverse_gram_differential_norm {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (L : E →L[ℝ] ℝ) :
    (∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j*L (b i)*L (b j))=‖L‖^2 := by
  let v := (InnerProductSpace.toDual ℝ E).symm L
  have hh := inverse_gram_contraction b v v
  have hv (i : ι) : inner ℝ (b i) v=L (b i) := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  simp only [hv,real_inner_self_eq_norm_sq] at hh
  have hn : ‖v‖=‖L‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map L
  rw [hn] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma round_centered_gradient_norm (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (q : Sphere 3) (U : Sphere 3 → ℝ)
    (hg : ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=inner ℝ
        (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4) (fun p : Sphere 3 => (p:Euclidean 4)) q v)
        (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4) (fun p : Sphere 3 => (p:Euclidean 4)) q w)) :
    Real.sqrt (coordinateGradientPair g U U q)=
      ‖fderiv ℝ (U ∘ (chartAt (Euclidean 3) q).symm) 0‖ := by
  rw [coordinateGradientPair,sphere_chart_center,round_metricCoefficients_at g q hg,
    inverse_gram_differential_norm,Real.sqrt_sq (norm_nonneg _)]

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma chart_inverse_differential_bound (g : SmoothMetric E M) (p : M) (y : E)
    (L : E →L[ℝ] ℝ) :
    (∑ i, ∑ j, (metricCoefficients g p y)⁻¹ i j*L (Module.finBasis ℝ E i)*L (Module.finBasis ℝ E j)) ≤
      chartInverseDifferentialBound g p y*‖L‖^2 := by
  unfold chartInverseDifferentialBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hi : |L (Module.finBasis ℝ E i)| ≤ ‖L‖*‖Module.finBasis ℝ E i‖ := L.le_opNorm _
  have hj : |L (Module.finBasis ℝ E j)| ≤ ‖L‖*‖Module.finBasis ℝ E j‖ := L.le_opNorm _
  calc
    _ ≤ |(metricCoefficients g p y)⁻¹ i j*L (Module.finBasis ℝ E i)*L (Module.finBasis ℝ E j)| :=
      le_abs_self _
    _ = |(metricCoefficients g p y)⁻¹ i j| *|L (Module.finBasis ℝ E i)| *|L (Module.finBasis ℝ E j)| := by
      rw [abs_mul,abs_mul]
    _ ≤ |(metricCoefficients g p y)⁻¹ i j| *(‖L‖*‖Module.finBasis ℝ E i‖)*
        (‖L‖*‖Module.finBasis ℝ E j‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hi (abs_nonneg _)) hj
        (abs_nonneg _) (mul_nonneg (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = _ := by ring

lemma chartInverseDifferentialBound_continuous (g : SmoothMetric E M) (p : M) :
    ContinuousOn (chartInverseDifferentialBound g p) (chartAt E p).target := by
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact (((contDiffOn_metricInverse g p i j).continuousOn.abs).mul continuousOn_const).mul continuousOn_const

theorem compact_chart_intrinsic_gradient_bound (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) :
    ∃ C > 0, ∀ (U : M → ℝ), ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ U → ∀ y ∈ K,
      Real.sqrt (coordinateGradientPair g U U ((chartAt E p).symm y)) ≤
        C*‖fderiv ℝ (U ∘ (chartAt E p).symm) y‖ := by
  obtain ⟨T,hT⟩ := hK.exists_bound_of_continuousOn
    ((chartInverseDifferentialBound_continuous g p).mono hKt)
  let C := Real.sqrt (max 1 T)
  have hC : 0 < C := Real.sqrt_pos.mpr (zero_lt_one.trans_le (le_max_left _ _))
  refine ⟨C,hC,?_⟩
  intro U hU y hy
  have hbound := chart_inverse_differential_bound g p y (fderiv ℝ (U ∘ (chartAt E p).symm) y)
  have hG : coordinateGradientPair g U U ((chartAt E p).symm y) ≤
      chartInverseDifferentialBound g p y*‖fderiv ℝ (U ∘ (chartAt E p).symm) y‖^2 := by
    rw [←localGradientPair_eq_global hU g p (hKt hy)]
    convert hbound using 1
    all_goals try with_reducible_and_instances rfl
    simp only [localGradientPair,dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hTb : chartInverseDifferentialBound g p y ≤ max 1 T :=
    (le_abs_self _).trans ((hT y hy).trans (le_max_right _ _))
  have hG' := hG.trans (mul_le_mul_of_nonneg_right hTb (sq_nonneg _))
  have hG0 := coordinateGradientPair_nonneg g U ((chartAt E p).symm y)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC.le (norm_nonneg _))).mp
  have hCsq : (C:ℝ)^2 = max 1 T := Real.sq_sqrt (zero_le_one.trans (le_max_left _ _))
  rw [Real.sq_sqrt hG0,mul_pow,hCsq]
  exact hG'

end



open Set Filter Function Manifold
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


end


section
open Set Filter Manifold
open scoped Topology ContDiff

theorem spherical_wave_centered_first_jet
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {r : ℝ} (hr : r < 1) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C > 0, ∀ (u : Euclidean 3 → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
        ((chartAt (Euclidean 3) sourcePole).symm y) < r} →
      ∀ (φ : Sphere 3 → ℝ) (n : ℕ), 1 ≤ n →
      (∀ y : Euclidean 3, ∀ j ≤ 1,
        ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(n:ℝ)^(j+4)*
          Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm y))) →
      ∀ q : Sphere 3,
        |sphericalWaveLift u q|+
          ‖fderiv ℝ (sphericalWaveLift u ∘ (chartAt (Euclidean 3) q).symm) 0‖/(n:ℝ) ≤
          C*(n:ℝ)^4*Real.exp ((n:ℝ)*φ q) := by
  let K := sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo r
  obtain ⟨C₁,hC₁,hgrad⟩ := compact_chart_intrinsic_gradient_bound g₀ sourcePole
    (sphericalCoverage_compact sourcePole sourceAxisOne sourceAxisTwo sphericalRadius_neg_sourcePole hr)
    (by rw [sphere_chart_target]; exact subset_univ _)
  refine ⟨C₀+C₁*C₀,by positivity,?_⟩
  intro u hu hc hs φ n hn hj q
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hUsm := sphericalWaveLift_smooth hu hc
  by_cases hq : sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r
  · let y := chartAt (Euclidean 3) sourcePole q
    have hqs := sphericalRadius_sublevel_in_source sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole hr hq
    have hy : y ∈ K := ⟨q,hq,rfl⟩
    have hqy : (chartAt (Euclidean 3) sourcePole).symm y=q :=
      (chartAt (Euclidean 3) sourcePole).left_inv hqs
    have he : sphericalWaveLift u ∘ (chartAt (Euclidean 3) sourcePole).symm=u :=
      funext (sphericalWaveLift_apply u)
    have hv := hj y 0 (by omega)
    have hd := hj y 1 (by omega)
    simp only [norm_iteratedFDeriv_zero,hqy,Nat.zero_add] at hv
    simp only [norm_iteratedFDeriv_one,hqy] at hd
    have hg := hgrad (sphericalWaveLift u) hUsm y hy
    rw [hqy,round_centered_gradient_norm g₀ q _ (hg₀ q),he] at hg
    have hval : sphericalWaveLift u q=u y := by rw [←hqy,sphericalWaveLift_apply]
    rw [hval]
    have hdiv := div_le_div_of_nonneg_right
      (hg.trans (mul_le_mul_of_nonneg_left hd hC₁.le)) hn0.le
    calc
      _ ≤ C₀*(n:ℝ)^4*Real.exp ((n:ℝ)*φ q)+
          (C₁*(C₀*(n:ℝ)^(1+4)*Real.exp ((n:ℝ)*φ q)))/(n:ℝ) := add_le_add hv hdiv
      _ = _ := by field_simp; ring
  · have hqs : q ∉ tsupport (sphericalWaveLift u) := fun h =>
      hq (show sphericalRadius sourceAxisOne sourceAxisTwo q < r from
        sphericalWaveLift_tsupport hc hs h).le
    have he : sphericalWaveLift u =ᶠ[𝓝 q] (fun _ => (0:ℝ)) :=
      notMem_tsupport_iff_eventuallyEq.mp hqs
    have hval : sphericalWaveLift u q=0 := he.eq_of_nhds
    have hchart : sphericalWaveLift u ∘ (chartAt (Euclidean 3) q).symm =ᶠ[𝓝 0]
        (fun _ => (0:ℝ)) := by
      apply he.comp_tendsto
      convert ((sphere_chart_symm_continuous q).continuousAt (x := (0 : Euclidean 3))).tendsto using 1
      all_goals try with_reducible_and_instances rfl
      have hz := (chartAt (Euclidean 3) q).left_inv (mem_chart_source (Euclidean 3) q)
      rw [sphere_chart_center] at hz
      rw [hz]
    rw [hval,(hchart.fderiv_eq)]
    have hright : 0 ≤ (C₀+C₁*C₀)*(n:ℝ)^4*Real.exp ((n:ℝ)*φ q) := by positivity
    simpa using hright

end


section
open Set Filter Manifold
open scoped Topology ContDiff

lemma sphericalWeight_pos (φ : Sphere 3 → ℝ) (n : ℕ) (q : Sphere 3) :
    0 < sphericalWeight φ n q := add_pos_of_pos_of_nonneg (Real.exp_pos _) (by positivity)

lemma spherical_global_exceptional_coverage {φ : Sphere 3 → ℝ}
    (hφ : Continuous φ) {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (hgap : ∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
      φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) :
    ∀ᶠ n : ℕ in atTop, ∀ q : Sphere 3,
      ‖planarLinear sourceAxisOne sourceAxisTwo q‖^n ≤ (n:ℝ)^6*Real.exp ((n:ℝ)*φ q) →
      sphericalRadius sourceAxisOne sourceAxisTwo q ≤ s := by
  let K : Set (Sphere 3) := {q | s ≤ sphericalRadius sourceAxisOne sourceAxisTwo q}
  have hK : IsCompact K := (isClosed_le continuous_const (sphericalRadius_continuous _ _)).isCompact
  filter_upwards [compact_exterior_background_domination hK
    (sphericalRadius_continuous sourceAxisOne sourceAxisTwo).continuousOn hφ.continuousOn
    (fun q hq => ht.trans_le (hts.le.trans hq))
    (fun q hq => hgap q (hts.trans_le hq)) 6] with n hn
  intro q hq
  by_contra h
  have hh := hn q (le_of_not_ge h)
  rw [sphericalRadius_eq_planar_norm] at hh
  exact (not_lt_of_ge hq) hh

end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_ExistsSphericalGlobalQuasimodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

theorem exists_spherical_global_quasimodes_oai
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {t s r : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r) (hr : r < 3/10)
    {F : Set (Sphere 3)} (hF : IsClosed F)
    (hFt : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q < t)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    (A : ℝ) :
    ∃ φ : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ ∧
      (∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
        sphericalRadius sourceAxisOne sourceAxisTwo q < t →
        Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q) ∧
      (∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
        φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) ∧
      ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
        (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
      ∀ (ι : Type) [Fintype ι] (p : ι → Sphere 3) (K : ι → Set (Euclidean 3)),
        (∀ i, IsCompact (K i)) → ∀ m D : ℕ, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
        ∃ u : Euclidean 3 → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
          tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
            ((chartAt (Euclidean 3) sourcePole).symm y) < r} ∧
          (∀ q : Sphere 3, sphericalWeight φ n q/(n:ℝ)^110 ≤
            |(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q|+
            Real.sqrt (coordinateGradientPair g
              (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u)
              (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q)/(n:ℝ)) ∧
          (∀ i, ∀ y ∈ K i, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j ((roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) ∘
              (chartAt (Euclidean 3) (p i)).symm) y‖ ≤
              C*(n:ℝ)^(j+4)*sphericalWeight φ n ((chartAt (Euclidean 3) (p i)).symm y) ∧
            ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
              (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
              sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q) ∘
              (chartAt (Euclidean 3) (p i)).symm) y‖ ≤
              C*(n:ℝ)^4/(n:ℝ)^D*sphericalWeight φ n ((chartAt (Euclidean 3) (p i)).symm y)) ∧
          ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
            (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
            (fun a => ε/((n:ℝ)*ℓ a.val))
            (((roundPower sourceAxisOne sourceAxisTwo n ∘
              (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) ∧
          ENNReal.ofReal (A*(n:ℝ)) < 36*Measure.hausdorffMeasure 2
            ((⋃ a : {J : Box (Fin 3) // J ∈ partition.boxes}, Box.Ioo a.val) ∩
              {x | ((roundPower sourceAxisOne sourceAxisTwo n ∘
                (chartAt (Euclidean 3) sourcePole).symm)+u) (normalWaveEquiv x)=0}) := by
  classical
  obtain ⟨φ,hφ,hin,hout,partition,hpart,ℓ,hℓ,ε,hε,hproduce⟩ :=
    exists_spherical_chart_quasimodes g₀ hg₀ g hg ht hts hsr hr A
  refine ⟨φ,hφ,hin,hout,partition,hpart,ℓ,hℓ,ε,hε,?_⟩
  intro ι _ p K hK m D
  obtain ⟨C₀,hC₀,hproduce⟩ := hproduce (max m 1) D
  have hbound (i : ι) := spherical_wave_background_chart_bounds g g₀ hg₀ hF hext hφ
    (fun q hq hz => hin q hz (hFt q hq)) (p i) (hK i) (by linarith : r<1) m D hC₀
  choose Cs hCs hb using hbound
  let C := 1+∑ i, Cs i
  have hC : 0 < C := by
    have hh : 0 ≤ ∑ i, Cs i := Finset.sum_nonneg (fun i _ => (hCs i).le)
    exact add_pos_of_pos_of_nonneg zero_lt_one hh
  have hCi (i : ι) : Cs i ≤ C := by
    have hh : Cs i ≤ ∑ j, Cs j := Finset.single_le_sum (fun j _ => (hCs j).le) (Finset.mem_univ i)
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  obtain ⟨Cc,hCc,hcenter⟩ := spherical_wave_centered_first_jet g₀ hg₀
    (by linarith : r < 1) C₀ hC₀
  have hfreq : ∀ᶠ n : ℕ in atTop, max 1 (2*Cc) ≤ (n:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (max 1 (2*Cc)))
  have hcover := spherical_global_exceptional_coverage hφ.continuous
    (by linarith : 0 < t) (by linarith : t < 3/10) hout
  refine ⟨C,hC,?_⟩
  filter_upwards [hproduce,eventually_all.mpr hb,hfreq,hcover,eventually_ge_atTop (2:ℕ)]
    with n hproduce hb hfreq hcover hn
  obtain ⟨u,hu,hc,hs,hj,hjet,hscore,hnod⟩ := hproduce
  have hn1 : 1 ≤ n := by omega
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn1
  have hnC : 2*Cc ≤ (n:ℝ)^2 := by
    have hCc' := (le_max_right (1:ℝ) (2*Cc)).trans hfreq
    nlinarith
  have hcenter' := hcenter u hu hc hs φ n hn1
    (fun y j hj1 => (hj y j (hj1.trans (le_max_right _ _))).1)
  have hlow := spherical_global_jet_lower g g₀ hg₀ hin hFt hext hmetric hn Cc hnC hcover
    hu hc hcenter' hjet
  refine ⟨u,hu,hc,hs,hlow,?_,hscore,hnod⟩
  intro i y hy j hjm
  have hbd := hb i u hu hc hs (fun y j hjm => hj y j (hjm.trans (le_max_left _ _))) y hy j hjm
  exact ⟨hbd.1.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hCi i) (by positivity)) (sphericalWeight_pos _ _ _).le),
    hbd.2.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hCi i) (by positivity)) (by positivity))
        (sphericalWeight_pos _ _ _).le)⟩


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_spherical_global_quasimodes_oai := @OAI.YauCounterexamples.exists_spherical_global_quasimodes_oai
