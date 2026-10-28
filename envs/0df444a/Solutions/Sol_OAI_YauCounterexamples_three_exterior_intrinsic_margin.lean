-- Prove2me | solution 1 for OAI.YauCounterexamples.three_exterior_intrinsic_margin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:37:35.247867+00:00
-- url     : https://prove2.me/submissions/4e3b98da-20ca-4568-bcb5-1ec6c5a72ffd

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_threeCoupled_global_noncancellation

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LpProductLinearMap
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
section LpProductJets
variable {E F A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
lemma lpProductFunction_hasFDerivAt {f : E → A} {g : F → B}
    {x : WithLp 2 (E×F)} {Df : E →L[ℝ] A} {Dg : F →L[ℝ] B}
    (hf : HasFDerivAt f Df x.fst) (hg : HasFDerivAt g Dg x.snd) :
    HasFDerivAt (lpProductFunction f g) (lpProductLinearMap Df Dg) x := by
  have hp := HasFDerivAt.prodMap (x.fst,x.snd) hf hg
  have hi := hp.comp x (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap.hasFDerivAt
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.toContinuousLinearMap.hasFDerivAt.comp x hi
end LpProductJets
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_LpProductFunctionMetric
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E F A B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
lemma lpProductRoundChart_first (p : A) (q : B) (L : E →ₗᵢ[ℝ] A) (K : F →ₗᵢ[ℝ] B) :
    HasFDerivAt (lpProductFunction (roundChart p L) (roundChart q K))
      (lpProductIsometry L K).toContinuousLinearMap 0 := by
  exact lpProductFunction_hasFDerivAt (roundChart_first p L) (roundChart_first q K)
end YauCounterexamples
end

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CutoffFactorCompactRaw
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_UnitSphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]

lemma unitSphere_chart_symm (p : Metric.sphere (0 : A) 1) :
    (fun y => ((chartAt (Euclidean n) p).symm y : A)) =
      roundChart (p : A) (unitSphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : A) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,unitSphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

lemma unitSphere_chart_center (p : Metric.sphere (0 : A) 1) : chartAt (Euclidean n) p p = 0 := by
  have hh : (chartAt (Euclidean n) p).symm 0 = p := by
    apply Subtype.ext
    change (fun y => ((chartAt (Euclidean n) p).symm y : A)) 0 = _
    rw [unitSphere_chart_symm,roundChart_zero]
  have hz : (0 : Euclidean n) ∈ (chartAt (Euclidean n) p).target := by
    change 0 ∈ (stereographic' n (-p)).target
    simp
  exact (congrArg (chartAt (Euclidean n) p) hh).symm.trans ((chartAt (Euclidean n) p).right_inv hz)

end


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_FourThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
local instance threeModelContinuousSMul : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma three_chart_symm (p : ThreeManifold) :
    threeImmersion ∘ (chartAt ThreeModel p).symm = threeChartMap p := by
  funext y
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · change ((chartAt (Euclidean 2) p.1).symm y.fst : Euclidean 3) = _
    exact congrFun (sphere_chart_symm p.1) y.fst
  · change ((chartAt (Euclidean 1) p.2).symm y.snd : ℂ) = _
    exact congrFun (unitSphere_chart_symm (n:=1) p.2) y.snd
lemma three_chart_center (p : ThreeManifold) : chartAt ThreeModel p p = 0 := by
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · exact sphere_chart_center p.1
  · exact unitSphere_chart_center (n:=1) p.2
attribute [local instance] OAI.YauCounterexamples.threeModelNormedSpace
lemma three_coordinate_embedding (p : ThreeManifold) (y v : ThreeModel) :
    mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion
      ((chartAt ThreeModel p).symm y)
      (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) (chartAt ThreeModel p).symm y v) =
        fderiv ℝ (threeChartMap p) y v := by
  have hy : y ∈ (chartAt ThreeModel p).target := by rw [three_chart_target]; trivial
  have hh := mfderiv_comp y
    (threeImmersion_smooth.mdifferentiable (by simp)).mdifferentiableAt
    ((contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (n := ∞) p) hy).mdifferentiableAt (by simp))
  have he := congrArg (fun L => L v) hh
  rw [mfderiv_eq_fderiv,three_chart_symm] at he
  exact he.symm
lemma three_metricCoefficients (p : ThreeManifold) (y : ThreeModel) (i j : CoordIndex ThreeModel) :
    metricCoefficients threeBackgroundMetric p y i j =
      inner ℝ (fderiv ℝ (threeChartMap p) y (Module.finBasis ℝ ThreeModel i))
        (fderiv ℝ (threeChartMap p) y (Module.finBasis ℝ ThreeModel j)) := by
  change (inner ℝ : ThreeAmbient → ThreeAmbient → ℝ) (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion ((chartAt ThreeModel p).symm y) (coordinateVector p y i)) (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion ((chartAt ThreeModel p).symm y) (coordinateVector p y j)) = _
  simp only [coordinateVector,three_coordinate_embedding]
lemma three_metricCoefficients_zero (p : ThreeManifold) :
    metricCoefficients threeBackgroundMetric p 0 = Matrix.gram ℝ (Module.finBasis ℝ ThreeModel) := by
  have hh : fderiv ℝ (threeChartMap p) 0 = (threeFrame p).toContinuousLinearMap :=
    (lpProductRoundChart_first (p.1:Euclidean 3) (p.2:ℂ) (sphereFrame p.1)
      (unitSphereFrame (n:=1) p.2)).fderiv
  ext i j
  rw [three_metricCoefficients,hh]
  exact (threeFrame p).inner_map_map _ _
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ProductFrequencyTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
attribute [local instance] OAI.YauCounterexamples.threeModelNormedSpace'
local instance threeModelContinuousSMul'_r908e04_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.threeAmbientNormedSpace'
local instance threeAmbientContinuousSMul'_r908e04_1 : ContinuousSMul ℝ ThreeAmbient := inferInstance
lemma threeComplexPower_smooth (a b : Euclidean 3) (k : ℕ) :
    ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℂ) ∞ (threeComplexPower a b k) := by
  let L : ThreeAmbient →L[ℝ] ℂ := (planarLinear a b).comp (WithLp.fstL 2 ℝ (Euclidean 3) ℂ)
  let R : ThreeAmbient →L[ℝ] ℂ := WithLp.sndL 2 ℝ (Euclidean 3) ℂ
  have hh : ContDiff ℝ ∞ (fun x : ThreeAmbient => (L x)^k*(R x)^k) :=
    (L.contDiff.pow k).mul (R.contDiff.pow k)
  have hc := hh.contMDiff.comp (I:=𝓘(ℝ,ThreeModel)) threeImmersion_smooth
  exact hc
lemma threePower_smooth (a b : Euclidean 3) (k : ℕ) :
    ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threePower a b k) :=
  Complex.reCLM.contMDiff.comp (threeComplexPower_smooth a b k)
end


section
open Set Filter
open scoped Topology

lemma productFrequency_nonneg (k : ℕ) : 0 ≤ productFrequency k := by
  unfold productFrequency
  positivity
lemma productWaveFrequency_bounds {k : ℕ} (hk : 1≤k) :
    (k:ℝ) ≤ productWaveFrequency k ∧ productWaveFrequency k ≤ 2*(k:ℝ) := by
  have hp : (1:ℝ)≤k := by exact_mod_cast hk
  have hs := Real.sq_sqrt (add_nonneg (productFrequency_nonneg k) zero_le_one)
  have hs0 := Real.sqrt_nonneg (productFrequency k+1)
  dsimp [productFrequency] at hs hs0 ⊢
  unfold productWaveFrequency productFrequency
  constructor <;> nlinarith [sq_nonneg ((k:ℝ)-1)]
lemma productWaveFrequency_tendsto : Tendsto productWaveFrequency atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) _ _)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
  exact (productWaveFrequency_bounds hk).1
end


open Set Filter Function Manifold
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ThreeCoupledNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
lemma threeCoupled_eq (r : ℝ) (k : ℕ) : threeCoupled r k =
    fun p => threePower (productAxis 0) (productAxis 1) k p+r^k*threePower (productAxis 0) (productAxis 2) k p := by
  funext p
  simp only [threeCoupled,threeCoupledComplex,add_mul,mul_assoc,Complex.add_re,
    ←Complex.ofReal_pow,Complex.re_ofReal_mul,threePower,threeComplexPower,productA,productB]
attribute [local instance] OAI.YauCounterexamples.threeCoupledNormedSpace
local instance threeCoupledContinuousSMul_r908e04_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeCoupled_smooth (r : ℝ) (k : ℕ) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeCoupled r k) := by
  rw [threeCoupled_eq]
  exact (threePower_smooth _ _ _).add (contMDiff_const.mul (threePower_smooth _ _ _))

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
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma three_chart_symm_continuous (p : ThreeManifold) : Continuous (chartAt ThreeModel p).symm := by
  exact continuousOn_univ.mp (by simpa only [OpenPartialHomeomorph.symm_source,three_chart_target] using
    (chartAt ThreeModel p).symm.continuousOn)
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
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
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeExceptional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma three_global_radius_weight_bound (k : ℕ) (p : ThreeManifold) :
    threeGlobalRadius p^k≤productWeight threeCouplingRadius k p ∧
    productWeight threeCouplingRadius k p≤2*threeGlobalRadius p^k := by
  have hr : 0≤threeCouplingRadius := by norm_num [threeCouplingRadius]
  have h1 := pow_le_pow_left₀ (norm_nonneg (productA p.1)) (le_max_left ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)) k
  have h2 := pow_le_pow_left₀ (mul_nonneg hr (norm_nonneg (productB p.1))) (le_max_right ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)) k
  rw [mul_pow] at h2
  constructor
  · dsimp [threeGlobalRadius,productWeight]
    rcases le_total ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖) with h|h
    · rw [max_eq_right h,mul_pow]; exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (by positivity)
  · dsimp [productWeight,threeGlobalRadius] at *; linarith

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsThreeScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma threeWaveLift_apply (u : NormalWaveSpace → ℝ) (y : NormalWaveSpace) :
    threeWaveLift u (threeNormalInv y)=u y := by
  dsimp [threeWaveLift,threeNormalInv]
  rw [manifoldChartPush_apply _ _ (by rw [three_chart_target]; trivial)]
  simp
attribute [local instance] OAI.YauCounterexamples.threeLiftNormedSpace
local instance threeLiftContinuousSMul_r908e04_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma threeWaveLift_smooth {u : NormalWaveSpace → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeWaveLift u) :=
  contMDiff_manifoldChartPush _ (hu.comp threeNormalEquiv.symm.contDiff)
    (hc.comp_homeomorph threeNormalEquiv.symm.toHomeomorph)
    (by rw [three_chart_target]; exact subset_univ _)
lemma threeWaveLift_tsupport {u : NormalWaveSpace → ℝ} (hc : HasCompactSupport u)
    {K : Set NormalWaveSpace} (hs : tsupport u⊆K) :
    tsupport (threeWaveLift u)⊆threeNormalInv '' K := by
  have he : threeWaveLift u=(fun p => threeNormalGlue 0 u p-0) := by
    funext p; simp [threeWaveLift,threeNormalGlue]
  rw [he]
  exact threeNormalGlue_tsupport 0 (by simpa using hc) (by simpa using hs)

lemma linearEquiv_comp_jets_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : F ≃L[ℝ] E) (m : ℕ) :
    ∃ C>0, ∀ (u : E → ℝ), ContDiff ℝ ∞ u → ∀ x : F, ∀ j  ≤  m, ∀ B : ℝ,
      0 ≤ B → ‖iteratedFDeriv ℝ j u (L x)‖ ≤ B → ‖iteratedFDeriv ℝ j (u ∘ L) x‖ ≤ C*B := by
  let c := max 1 ‖L.toContinuousLinearMap‖
  refine ⟨c^m, pow_pos (zero_lt_one.trans_le (le_max_left _ _)) _,?_⟩
  intro u hu x j hj B hB hb
  change ‖iteratedFDeriv ℝ j (u ∘ L.toContinuousLinearMap) x‖ ≤ _
  rw [L.toContinuousLinearMap.iteratedFDeriv_comp_right hu x (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))]
  have hn := (iteratedFDeriv ℝ j u (L x)).norm_compContinuousLinearMap_le (fun _ : Fin j => L.toContinuousLinearMap)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hn
  have hp : ‖L.toContinuousLinearMap‖^j ≤ c^m :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans (pow_le_pow_right₀ (le_max_left _ _) hj)
  exact hn.trans ((mul_le_mul hb hp (by positivity) hB).trans_eq (mul_comm _ _))

end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
attribute [local instance] OAI.YauCounterexamples.threeGlobalResidualNormedSpace
local instance threeGlobalResidualContinuousSMul_r908e04_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma three_chart_pullback_smooth {f : ThreeManifold → ℝ}
    (hf : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ f) (p : ThreeManifold) :
    ContDiff ℝ ∞ (f ∘ (chartAt ThreeModel p).symm) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  exact contDiffAt_inChart hf p (by rw [three_chart_target]; trivial)
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
attribute [local instance] OAI.YauCounterexamples.threeCenteredWaveNormedSpace
local instance threeCenteredWaveContinuousSMul_r908e04_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma three_centered_gradient_norm (p : ThreeManifold) (U : ThreeManifold → ℝ) :
    Real.sqrt (coordinateGradientPair threeBackgroundMetric U U p)=
      ‖fderiv ℝ (U ∘ (chartAt ThreeModel p).symm) 0‖ := by
  rw [coordinateGradientPair,three_chart_center,three_metricCoefficients_zero,
    inverse_gram_differential_norm,Real.sqrt_sq (norm_nonneg _)]
lemma three_centered_gradient_norm_of_agree (g : SmoothMetric ThreeModel ThreeManifold)
    (p : ThreeManifold) (U : ThreeManifold → ℝ)
    (hg : ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) p,
      g.inner p v w=threeBackgroundMetric.inner p v w) :
    Real.sqrt (coordinateGradientPair g U U p)=
      ‖fderiv ℝ (U ∘ (chartAt ThreeModel p).symm) 0‖ := by
  have he : coordinateGradientPair g U U p=coordinateGradientPair threeBackgroundMetric U U p := by
    have hm : metricCoefficients g p (chartAt ThreeModel p p)=
        metricCoefficients threeBackgroundMetric p (chartAt ThreeModel p p) := by
      ext i j
      dsimp [metricCoefficients]
      rw [(chartAt ThreeModel p).left_inv (mem_chart_source ThreeModel p)]
      exact hg _ _
    simp only [coordinateGradientPair,hm]
  rw [he,three_centered_gradient_norm]

lemma three_wave_centered_first_jet (r : ℝ) (C₀ : ℝ) (hC₀ : 0<C₀) :
    ∃ C>0, ∀ (u : NormalWaveSpace → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u⊆closedBall 0 r → ∀ (φ : ThreeManifold → ℝ) (k : ℕ), 1 ≤ k →
      (∀ y : NormalWaveSpace, ∀ j ≤ 1,
        ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(k:ℝ)^(j+4)*
          Real.exp (productWaveFrequency k*φ (threeNormalInv y))) →
      ∀ p : ThreeManifold, |threeWaveLift u p|+
        ‖fderiv ℝ (threeWaveLift u ∘ (chartAt ThreeModel p).symm) 0‖/(k:ℝ) ≤
          C*(k:ℝ)^4*Real.exp (productWaveFrequency k*φ p) := by
  let K := threeNormalEquiv '' closedBall 0 r
  have hK : IsCompact K := (isCompact_closedBall _ _).image threeNormalEquiv.continuous
  obtain ⟨C₁,hC₁,hgrad⟩ := compact_chart_intrinsic_gradient_bound threeBackgroundMetric threeProfileCenter hK
    (by rw [three_chart_target]; exact subset_univ _)
  obtain ⟨D,hD,hlin⟩ := linearEquiv_comp_jets_bound threeNormalEquiv.symm 1
  refine ⟨C₀+C₁*D*C₀,by positivity,?_⟩
  intro u hu hc hs φ k hk hj p
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hUsm := threeWaveLift_smooth hu hc
  by_cases hp : p∈threeNormalInv '' closedBall 0 r
  · obtain ⟨y,hy,rfl⟩ := hp
    have he : threeWaveLift u ∘ (chartAt ThreeModel threeProfileCenter).symm=u ∘ threeNormalEquiv.symm := by
      funext z
      have h := threeWaveLift_apply u (threeNormalEquiv.symm z)
      simpa only [threeNormalInv,Function.comp_apply,threeNormalEquiv.apply_symm_apply] using h
    have hgrad' := hgrad (threeWaveLift u) hUsm (threeNormalEquiv y) ⟨y,hy,rfl⟩
    change Real.sqrt (coordinateGradientPair threeBackgroundMetric _ _ (threeNormalInv y)) ≤ _ at hgrad'
    rw [three_centered_gradient_norm,he] at hgrad'
    have hder := hlin u hu (threeNormalEquiv y) 1 le_rfl
      (C₀*(k:ℝ)^5*Real.exp (productWaveFrequency k*φ (threeNormalInv y))) (by positivity)
      (by simpa only [threeNormalEquiv.symm_apply_apply] using hj y 1 le_rfl)
    rw [norm_iteratedFDeriv_one] at hder
    have hval := hj y 0 (by omega)
    simp only [norm_iteratedFDeriv_zero,Nat.zero_add,Real.norm_eq_abs] at hval
    rw [threeWaveLift_apply]
    calc
      _ ≤ C₀*(k:ℝ)^4*Real.exp (productWaveFrequency k*φ (threeNormalInv y))+
          C₁*(D*(C₀*(k:ℝ)^5*Real.exp (productWaveFrequency k*φ (threeNormalInv y))))/(k:ℝ) :=
        add_le_add hval (div_le_div_of_nonneg_right (hgrad'.trans (mul_le_mul_of_nonneg_left hder hC₁.le)) hk0.le)
      _ = _ := by field_simp
  · have hps : p∉tsupport (threeWaveLift u) := fun h => hp (threeWaveLift_tsupport hc hs h)
    have he : threeWaveLift u =ᶠ[𝓝 p] (fun _ => (0:ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hps
    have hval := he.eq_of_nhds
    have ht : Tendsto (chartAt ThreeModel p).symm (𝓝 (0:ThreeModel)) (𝓝 p) := by
      have hh := (three_chart_symm_continuous p).tendsto 0
      simpa only [←three_chart_center p,(chartAt ThreeModel p).left_inv (mem_chart_source ThreeModel p)] using hh
    have hz : threeWaveLift u ∘ (chartAt ThreeModel p).symm =ᶠ[𝓝 (0:ThreeModel)] (fun _ => (0:ℝ)) := ht.eventually he
    rw [hval,hz.fderiv_eq]
    simp only [fderiv_fun_const]
    simp only [Pi.zero_apply,abs_zero,norm_zero,zero_div,zero_add]
    positivity
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff

lemma weighted_exterior_absorption {ν C E P J V : ℝ} (hν : 1 ≤ ν) (_hC : 0 ≤ C)
    (hE : 0 ≤ E) (_hJ : 0 ≤ J) (hV : V ≤ C*ν^4*E) (hP : ν^6*E<P)
    (hback : P ≤ 24*(J+V)) (hsmall : 48*C ≤ ν^2) : P ≤ 48*J := by
  have hs : 48*(C*ν^4*E) ≤ ν^6*E := by
    calc
      _ = (48*C)*ν^4*E := by ring
      _  ≤  ν^2*ν^4*E := by gcongr
      _ = _ := by ring
  have hh : 48*V<P := (mul_le_mul_of_nonneg_left hV (by norm_num)).trans_lt (hs.trans_lt hP)
  linarith

lemma three_exterior_intrinsic_margin_oai (g : SmoothMetric ThreeModel ThreeManifold)
    {φ : ThreeManifold → ℝ} (r C₀ : ℝ) (hC₀ : 0<C₀) :
    ∀ᶠ k : ℕ in atTop, ∀ u : NormalWaveSpace → ℝ,
      ContDiff ℝ ∞ u → HasCompactSupport u → tsupport u⊆closedBall 0 r →
      (∀ y : NormalWaveSpace, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(k:ℝ)^(j+4)*
        Real.exp (productWaveFrequency k*φ (threeNormalInv y))) →
      ∀ p∉threeExceptional φ k,
      (∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) p, g.inner p v w=threeBackgroundMetric.inner p v w) →
      let U := threeCoupled threeCouplingRadius k+threeWaveLift u
      threeWeight φ k p/productWaveFrequency k^111 ≤ |U p|+
        Real.sqrt (coordinateGradientPair g U U p)/productWaveFrequency k := by
  obtain ⟨C,hC,hfirst⟩ := three_wave_centered_first_jet r C₀ hC₀
  have hf := productWaveFrequency_tendsto.eventually (eventually_ge_atTop (max 96 (48*C+1)))
  filter_upwards [hf,eventually_ge_atTop (2:ℕ)] with k hνlarge hk
  intro u hu hc hs hj p hp hagree
  dsimp only
  let ν := productWaveFrequency k
  let v := threeWaveLift u
  let w := threeCoupled threeCouplingRadius k
  let U := w+v
  let D (f : ThreeManifold → ℝ) := fderiv ℝ (f ∘ (chartAt ThreeModel p).symm) 0
  let J (f : ThreeManifold → ℝ) := |f p|+‖D f‖/ν
  have hk1 : 1 ≤ k := by omega
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hνb := productWaveFrequency_bounds hk1
  have hν96 : 96 ≤ ν := (le_max_left _ _).trans hνlarge
  have hνC : 48*C+1 ≤ ν := (le_max_right _ _).trans hνlarge
  have hν1 : 1 ≤ ν := by linarith
  have hν0 : 0<ν := by linarith
  have hvsm := threeWaveLift_smooth hu hc
  have hwsm := threeCoupled_smooth threeCouplingRadius k
  have hD : D U=D w+D v := by
    exact fderiv_add ((three_chart_pullback_smooth hwsm p).differentiable (by simp) 0)
      ((three_chart_pullback_smooth hvsm p).differentiable (by simp) 0)
  have htri : J w ≤ J U+J v := by
    have ha : |w p| ≤ |U p|+|v p| := by
      have h := norm_sub_le (U p) (v p)
      simpa only [Real.norm_eq_abs,U,Pi.add_apply,add_sub_cancel_right] using h
    have hd : ‖D w‖ ≤ ‖D U‖+‖D v‖ := by
      have he : D w=D U-D v := by rw [hD]; simp only [add_sub_cancel_right]
      rw [he]; exact norm_sub_le _ _
    dsimp [J]
    have hh := div_le_div_of_nonneg_right hd hν0.le
    rw [add_div] at hh
    linarith
  have hback₀ := threeCoupled_global_noncancellation (r:=threeCouplingRadius) (by norm_num [threeCouplingRadius])
    (by norm_num [threeCouplingRadius]) k hk p
  have hr : ‖D w‖/(k:ℝ) ≤ 2*(‖D w‖/ν) := by
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hk0 hν0).mpr
    have hh := mul_le_mul_of_nonneg_left hνb.2 (norm_nonneg (D w))
    nlinarith
  have hback : productWeight threeCouplingRadius k p ≤ 24*(J U+J v) := by
    have h1 : productWeight threeCouplingRadius k p ≤ 24*J w := by
      change _ ≤ 24*(|w p|+‖D w‖/ν)
      change _ ≤ 12*(|w p|+‖D w‖/(k:ℝ)) at hback₀
      nlinarith [abs_nonneg (w p)]
    exact h1.trans (mul_le_mul_of_nonneg_left htri (by norm_num))
  have hfirst' := hfirst u hu hc hs φ k hk1 hj p
  have hv : J v ≤ C*ν^4*Real.exp (ν*φ p) := by
    have hd : ‖D v‖/ν ≤ ‖D v‖/(k:ℝ) := div_le_div_of_nonneg_left (norm_nonneg _) hk0 hνb.1
    have hpow := pow_le_pow_left₀ hk0.le hνb.1 4
    exact (add_le_add (le_refl |v p|) hd).trans (hfirst'.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) (Real.exp_pos _).le))
  have hP : ν^6*Real.exp (ν*φ p)<productWeight threeCouplingRadius k p := lt_of_not_ge hp
  have hJ : 0 ≤ J U := by dsimp [J]; positivity
  have hsmall : 48*C ≤ ν^2 := by nlinarith
  have habs := weighted_exterior_absorption hν1 hC.le (Real.exp_pos _).le hJ hv hP hback hsmall
  have hν6 : 1 ≤ ν^6 := one_le_pow₀ hν1
  have hE : Real.exp (ν*φ p) ≤ productWeight threeCouplingRadius k p :=
    (le_mul_of_one_le_left (Real.exp_pos _).le hν6).trans hP.le
  have hW : threeWeight φ k p ≤ 96*J U := by
    have hr := (three_global_radius_weight_bound k p).1
    dsimp [threeWeight]
    linarith
  have hpow : 96 ≤ ν^111 := hν96.trans (le_self_pow₀ hν1 (by omega : 111≠0))
  rw [three_centered_gradient_norm_of_agree g p _ hagree]
  apply (div_le_iff₀ (pow_pos hν0 111)).mpr
  exact hW.trans (by dsimp [J,D,U,w,v,ν] at *; nlinarith)
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.three_exterior_intrinsic_margin_oai := @OAI.YauCounterexamples.three_exterior_intrinsic_margin_oai
