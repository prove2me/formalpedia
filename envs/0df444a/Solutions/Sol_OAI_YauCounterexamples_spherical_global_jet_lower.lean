-- Prove2me | solution 1 for OAI.YauCounterexamples.spherical_global_jet_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:47:39.737634+00:00
-- url     : https://prove2.me/submissions/a3fed7f7-28d5-4e6d-9587-a68ec8ba36ff

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007
import Definitions.Def_OAIQ070A008

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma selfMetricFlat_apply (g : SmoothMetric E E) (x v w : E) :
    selfMetricFlat g x v w = g.inner x v w := rfl


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

lemma roundChart_smooth (p : E) (L : F →ₗᵢ[ℝ] E) : ContDiff ℝ ∞ (roundChart p L) :=
  contDiff_stereoInvFunAux.comp L.contDiff

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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma roundLinearPower_directional (ℓ : E →L[ℝ] ℂ) (n : ℕ) (p : E)
    (L : F →ₗᵢ[ℝ] E) (x w : F) :
    fderiv ℝ (fun y => (ℓ (roundChart p L y))^n) x w =
      (n:ℂ) * (ℓ (roundChart p L x))^(n-1) * ℓ (fderiv ℝ (roundChart p L) x w) := by
  have hc := ((roundChart_smooth p L).differentiable (by simp) x).hasFDerivAt
  have hh := (ℓ.hasFDerivAt.comp x hc).pow n
  convert! congrArg (fun D => D w) hh.fderiv using 1
  all_goals try with_reducible_and_instances rfl
  simp [smul_eq_mul,mul_assoc]

lemma fderiv_real_part {f : F → ℂ} {x : F} (hf : DifferentiableAt ℝ f x) (v : F) :
    fderiv ℝ (fun y => (f y).re) x v = (fderiv ℝ f x v).re := by
  have hh := Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt
  convert! congrArg (fun D => D v) hh.fderiv using 1
  all_goals try with_reducible_and_instances rfl




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
lemma sphereFrame_orthogonal (p : Sphere n) (w : Euclidean n) :
    inner ℝ (p : Euclidean (n+1)) (sphereFrame p w) = 0 := by
  have hh := ((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm w).property
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hh
  change inner ℝ (p : Euclidean (n+1)) _ = 0
  rw [real_inner_comm]
  change inner ℝ _ (-(p : Euclidean (n+1))) = 0 at hh
  rw [inner_neg_right,neg_eq_zero] at hh
  exact hh

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

attribute [local instance] OAI.YauCounterexamples.instFactEqNatFinrankRealEuclideanHAddOfNat_1
lemma sphereFrame_coordinates (p : Sphere n) (a : Euclidean (n+1)) :
    sphereFrame p (sphereCoordinates p a) = sphereProjection p a := by
  change (((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm
      ((OrthonormalBasis.fromOrthogonalSpanSingleton n
        (ne_zero_of_mem_unit_sphere (-p))).repr ⟨sphereProjection p a,_⟩)) : Euclidean (n+1)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

lemma sphereCoordinates_inner (p : Sphere n) (a b : Euclidean (n+1)) :
    inner ℝ (sphereCoordinates p a) (sphereCoordinates p b) =
      inner ℝ a b - inner ℝ (p : Euclidean (n+1)) a * inner ℝ (p : Euclidean (n+1)) b := by
  rw [← (sphereFrame p).inner_map_map,sphereFrame_coordinates,sphereFrame_coordinates]
  simp [sphereProjection,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    real_inner_comm a (p : Euclidean (n+1))]

lemma sphereFrame_inner (p : Sphere n) (a : Euclidean (n+1)) (w : Euclidean n) :
    inner ℝ (sphereFrame p w) a = inner ℝ w (sphereCoordinates p a) := by
  rw [← (sphereFrame p).inner_map_map,sphereFrame_coordinates]
  have hh := sphereFrame_orthogonal p w
  rw [real_inner_comm] at hh
  simp [sphereProjection,inner_sub_right,inner_smul_right,hh]

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SphericalBaseProfileRadius
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
variable {n : ℕ}

lemma sphereChartMetric_pairing (g : SmoothMetric (Euclidean n) (Sphere n))
    (p : Sphere n) (y v w : Euclidean n) :
    (sphereChartMetric g p).inner y v w = chartMetricForm g p y v w := rfl


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffSmoothFiniteWave
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma normalWaveEquiv_single (i : Fin 3) :
    normalWaveEquiv (Pi.single i 1) = EuclideanSpace.basisFun (Fin 3) ℝ i := by
  rw [EuclideanSpace.basisFun_apply]
  rfl


end

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
open Set Filter
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
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

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

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

lemma ambientPowerGradient_pair (a b : Euclidean (d+1)) (k : ℕ) (x v : Euclidean (d+1)) :
    inner ℝ v (ambientPowerGradient a b k x) =
      ((k:ℂ) * (planarLinear a b x)^(k-1) * planarLinear a b v).re := by
  simp only [ambientPowerGradient,inner_smul_right,inner_sub_right,
    planarLinear_apply,Complex.mul_re,Complex.mul_im,Complex.natCast_re,
    Complex.natCast_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,
    zero_add,add_zero,one_mul]
  rw [real_inner_comm a v,real_inner_comm b v]
  ring

lemma roundPower_chart_directional (a b : Euclidean (d+1)) (k : ℕ) (p : Sphere d) (v : Euclidean d) :
    fderiv ℝ (roundPower a b k ∘ (chartAt (Euclidean d) p).symm) 0 v =
      inner ℝ (sphereFrame p v) (ambientPowerGradient a b k p) := by
  have hc : roundPower a b k ∘ (chartAt (Euclidean d) p).symm =
      fun z => ((planarLinear a b (roundChart (p : Euclidean (d+1)) (sphereFrame p) z))^k).re := by
    funext z
    simp only [roundPower,Function.comp_apply]
    rw [← sphere_chart_symm]
  have hf : ContDiff ℝ ∞ (fun z => (planarLinear a b (roundChart (p : Euclidean (d+1)) (sphereFrame p) z))^k) :=
    ((planarLinear a b).contDiff.comp (roundChart_smooth _ _)).pow k
  rw [hc,fderiv_real_part (hf.differentiable (by simp) _),roundLinearPower_directional,
    roundChart_zero,(roundChart_first _ _).fderiv,ambientPowerGradient_pair]
  rfl

lemma ambientPowerGradient_norm_sq (a b : Euclidean (d+1)) (k : ℕ) (x : Euclidean (d+1))
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    inner ℝ (ambientPowerGradient a b k x) (ambientPowerGradient a b k x) =
      (k:ℝ)^2 * (Complex.normSq (planarLinear a b x))^(k-1) := by
  have hba : inner ℝ b a = 0 := (real_inner_comm a b).trans hab
  simp only [ambientPowerGradient,inner_smul_left,inner_smul_right,inner_sub_left,
    inner_sub_right,ha,hb,hab,hba,conj_trivial,mul_one,mul_zero,sub_zero,zero_sub]
  rw [← map_pow Complex.normSq]
  simp only [Complex.normSq_apply]
  ring

lemma ambientPowerGradient_radial (a b : Euclidean (d+1)) (k : ℕ) (hk : 1 ≤ k) (x : Euclidean (d+1)) :
    inner ℝ x (ambientPowerGradient a b k x) = (k:ℝ) * ((planarLinear a b x)^k).re := by
  rw [ambientPowerGradient_pair,mul_assoc,← pow_succ,Nat.sub_add_cancel hk]
  simp [Complex.mul_re]


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

end



open Set Filter Function Manifold
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_RoundPowerExteriorPerturbationJet
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
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}

lemma roundPower_centered_derivative_square (a b : Euclidean (d+1)) (n : ℕ)
    (hn : 1 ≤ n) (ha : inner ℝ a a=1) (hb : inner ℝ b b=1)
    (hab : inner ℝ a b=0) (p : Sphere d) :
    ‖fderiv ℝ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) 0‖^2 =
      (n:ℝ)^2*(Complex.normSq (planarLinear a b p)^(n-1)-(roundPower a b n p)^2) := by
  have he : fderiv ℝ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) 0 =
      innerSL ℝ (sphereCoordinates p (ambientPowerGradient a b n p)) := by
    ext v
    rw [roundPower_chart_directional,sphereFrame_inner]
    simp only [innerSL_apply_apply,real_inner_comm]
  rw [he,innerSL_apply_norm,←real_inner_self_eq_norm_sq,sphereCoordinates_inner,
    ambientPowerGradient_norm_sq _ _ _ _ ha hb hab,ambientPowerGradient_radial _ _ _ hn]
  simp only [roundPower]
  ring

theorem roundPower_centered_jet_lower (a b : Euclidean (d+1)) (n : ℕ)
    (hn : 1 ≤ n) (ha : inner ℝ a a=1) (hb : inner ℝ b b=1)
    (hab : inner ℝ a b=0) (p : Sphere d) :
    ‖planarLinear a b p‖^n ≤ |roundPower a b n p|+
      ‖fderiv ℝ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) 0‖/(n:ℝ) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hr : Complex.normSq (planarLinear a b p) ≤ 1 := by
    have horth : inner ℝ b a=0 := (real_inner_comm a b).trans hab
    let x : Euclidean (d+1) := p
    have hs := real_inner_self_nonneg (x := x - (inner ℝ a x • a + inner ℝ b x • b))
    have hx : inner ℝ x x=1 := by
      rw [real_inner_self_eq_norm_sq]
      have hp : ‖(p : Euclidean (d+1))‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.property
      dsimp [x]; rw [hp]; norm_num
    simp only [inner_sub_left,inner_sub_right,inner_add_left,inner_add_right,
      inner_smul_left,inner_smul_right,ha,hb,hab,horth,hx,mul_one,mul_zero,add_zero,
      zero_add,conj_trivial] at hs
    have hre : (planarLinear a b p).re = inner ℝ a x := by simp [planarLinear_apply,x]
    have him : (planarLinear a b p).im = inner ℝ b x := by simp [planarLinear_apply,x]
    rw [Complex.normSq_apply,hre,him]
    rw [real_inner_comm a x,real_inner_comm b x] at hs
    nlinarith
  have hR0 := Complex.normSq_nonneg (planarLinear a b p)
  have hp : Complex.normSq (planarLinear a b p)^n ≤ Complex.normSq (planarLinear a b p)^(n-1) := by
    calc
      _ = Complex.normSq (planarLinear a b p)^(n-1)*Complex.normSq (planarLinear a b p) := by
        rw [←pow_succ,Nat.sub_add_cancel hn]
      _ ≤ _ := mul_le_of_le_one_right (pow_nonneg hR0 _) hr
  have hsq := roundPower_centered_derivative_square a b n hn ha hb hab p
  have he : (‖fderiv ℝ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) 0‖/(n:ℝ))^2 =
      Complex.normSq (planarLinear a b p)^(n-1)-(roundPower a b n p)^2 := by
    rw [div_pow,hsq]; field_simp
  have heN : (‖planarLinear a b p‖^n)^2 = Complex.normSq (planarLinear a b p)^n := by
    rw [←pow_mul, Nat.mul_comm n 2, pow_mul,Complex.sq_norm]
  have hw := abs_nonneg (roundPower a b n p)
  have hv : 0 ≤ ‖fderiv ℝ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) 0‖/(n:ℝ) := by positivity
  have hrn : 0 ≤ ‖planarLinear a b p‖^n := pow_nonneg (norm_nonneg _) _
  have hw2 := sq_abs (roundPower a b n p)
  nlinarith [mul_nonneg hw hv]

theorem roundPower_dominant_perturbation_jet_lower (a b : Euclidean (d+1)) (n : ℕ)
    (hn : 1 ≤ n) (ha : inner ℝ a a=1) (hb : inner ℝ b b=1)
    (hab : inner ℝ a b=0) (p : Sphere d) (v : Sphere d → ℝ)
    (hv : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ v)
    (t C : ℝ) (hnC : 2*C ≤ (n:ℝ)^2)
    (hdom : (n:ℝ)^6*Real.exp ((n:ℝ)*t) ≤ ‖planarLinear a b p‖^n)
    (hsmall : |v p|+‖fderiv ℝ (v ∘ (chartAt (Euclidean d) p).symm) 0‖/(n:ℝ) ≤
      C*(n:ℝ)^4*Real.exp ((n:ℝ)*t)) :
    (Real.exp ((n:ℝ)*t)+‖planarLinear a b p‖^n)/4 ≤
      |roundPower a b n p+v p|+
      ‖fderiv ℝ ((roundPower a b n+v) ∘ (chartAt (Euclidean d) p).symm) 0‖/(n:ℝ) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := zero_lt_one.trans_le hn1
  have hhalf : C*(n:ℝ)^4*Real.exp ((n:ℝ)*t) ≤ ‖planarLinear a b p‖^n/2 := by
    have hh := mul_le_mul_of_nonneg_right hnC
      (show 0 ≤ (n:ℝ)^4*Real.exp ((n:ℝ)*t) by positivity)
    have he : (n:ℝ)^2*((n:ℝ)^4*Real.exp ((n:ℝ)*t)) =
        (n:ℝ)^6*Real.exp ((n:ℝ)*t) := by ring
    rw [he] at hh
    nlinarith
  have hex : Real.exp ((n:ℝ)*t) ≤ ‖planarLinear a b p‖^n := by
    calc
      _ ≤ (n:ℝ)^6*Real.exp ((n:ℝ)*t) := le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ hn1)
      _ ≤ _ := hdom
  have hlower := roundPower_centered_jet_lower a b n hn ha hb hab p
  have habs : |roundPower a b n p| ≤ |roundPower a b n p+v p|+|v p| := by
    simpa only [Real.norm_eq_abs, add_neg_cancel_right,abs_neg] using norm_add_le (roundPower a b n p+v p) (-v p)
  have hzero : (0 : Euclidean d) ∈ (chartAt (Euclidean d) p).target := by
    rw [sphere_chart_target]; trivial
  have hD₁ := (contDiffAt_inChart (roundPower_smooth a b n) p hzero).differentiableAt (by simp)
  have hD₂ := (contDiffAt_inChart hv p hzero).differentiableAt (by simp)
  have heq : ((roundPower a b n+v) ∘ (chartAt (Euclidean d) p).symm) =
      (roundPower a b n ∘ (chartAt (Euclidean d) p).symm)+(v ∘ (chartAt (Euclidean d) p).symm) := rfl
  rw [heq,fderiv_add hD₁ hD₂]
  let A := fderiv ℝ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) 0
  let B := fderiv ℝ (v ∘ (chartAt (Euclidean d) p).symm) 0
  have hd : ‖A‖ ≤ ‖A+B‖+‖B‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (A+B) B
  have hdiv := div_le_div_of_nonneg_right hd hn0.le
  rw [add_div] at hdiv
  change (Real.exp ((n:ℝ)*t)+‖planarLinear a b p‖^n)/4 ≤
    |roundPower a b n p+v p|+‖A+B‖/(n:ℝ)
  change ‖planarLinear a b p‖^n ≤ |roundPower a b n p|+‖A‖/(n:ℝ) at hlower
  change |v p|+‖B‖/(n:ℝ) ≤ _ at hsmall
  linarith

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
open scoped Topology ContDiff Manifold InnerProductSpace


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

section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
omit [FiniteDimensional ℝ E] in
lemma scalarDifferential_chart_vector {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) (v : E) :
    scalarDifferential u ((chartAt E p).symm y)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y v) =
      fderiv ℝ (u ∘ (chartAt E p).symm) y v := by
  have hc : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y :=
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy
      (n := ∞)).mdifferentiableAt (by simp)
  have he := mfderiv_comp y (hu.mdifferentiable (by simp) _) hc
  rw [mfderiv_eq_fderiv] at he
  exact (congrArg (fun T => T v) he).symm

lemma chart_derivative_dual_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) (v : E) :
    (fderiv ℝ (u ∘ (chartAt E p).symm) y v)^2 ≤
      coordinateGradientPair g u u ((chartAt E p).symm y)*chartMetricForm g p y v v := by
  have hh := scalarDifferential_dual_bound hu g ((chartAt E p).symm y)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y v)
  rw [scalarDifferential_chart_vector hu p hy] at hh
  simpa only [chartMetricForm_pairing] using hh
end

lemma realWaveJet_intrinsic_upper {U : Sphere 3 → ℝ}
    (hU : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ U)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (p : Sphere 3)
    {n W : ℝ} (hn : 0 < n) (hW : 0 < W) (x : Fin 3 → ℝ)
    (hmetric : ∀ v : Euclidean 3,
      selfMetricFlat (sphereChartMetric g p) (normalWaveEquiv x) v v ≤ ‖v‖^2) :
    ‖realWaveJet n W ((U ∘ (chartAt (Euclidean 3) p).symm) ∘ normalWaveEquiv) x‖ ≤
      (|U ((chartAt (Euclidean 3) p).symm (normalWaveEquiv x))|+
        Real.sqrt (coordinateGradientPair g U U ((chartAt (Euclidean 3) p).symm
          (normalWaveEquiv x)))/n)/W := by
  let q := (chartAt (Euclidean 3) p).symm (normalWaveEquiv x)
  let F := U ∘ (chartAt (Euclidean 3) p).symm
  have hF : ContDiff ℝ ∞ F := spherical_chart_pullback_smooth hU p
  have hG : 0 ≤ coordinateGradientPair g U U q := coordinateGradientPair_nonneg g U q
  have hder (i : Fin 3) : |fderiv ℝ (F ∘ normalWaveEquiv) x (Pi.single i 1)| ≤
      Real.sqrt (coordinateGradientPair g U U q) := by
    have hd := chart_derivative_dual_bound hU g p
      (show normalWaveEquiv x ∈ (chartAt (Euclidean 3) p).target by rw [sphere_chart_target]; trivial)
      (normalWaveEquiv (Pi.single i 1))
    have hm := hmetric (normalWaveEquiv (Pi.single i 1))
    rw [normalWaveEquiv_single, (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one, one_pow] at hm
    have hd' : (fderiv ℝ F (normalWaveEquiv x) (normalWaveEquiv (Pi.single i 1)))^2 ≤
        coordinateGradientPair g U U q := by
      exact hd.trans ((mul_le_mul_of_nonneg_left
        (show chartMetricForm g p (normalWaveEquiv x) (normalWaveEquiv (Pi.single i 1))
          (normalWaveEquiv (Pi.single i 1)) ≤ 1 from by simpa only [normalWaveEquiv_single,selfMetricFlat_apply,sphereChartMetric_pairing] using hm) hG).trans_eq (mul_one _))
    have he := (hF.differentiable (by simp) _).hasFDerivAt.comp x normalWaveEquiv.hasFDerivAt
    have he' := congrArg (fun T => T (Pi.single i 1)) he.fderiv
    change fderiv ℝ (F ∘ normalWaveEquiv) x (Pi.single i 1) =
      fderiv ℝ F (normalWaveEquiv x) (normalWaveEquiv (Pi.single i 1)) at he'
    rw [he']
    exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
      (by rw [sq_abs,Real.sq_sqrt hG]; exact hd')
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rcases i with i|i
  · change ‖W⁻¹*U q‖ ≤ (|U q|+Real.sqrt (coordinateGradientPair g U U q)/n)/W
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hW),Real.norm_eq_abs]
    rw [mul_comm W⁻¹,←div_eq_mul_inv]
    apply div_le_div_of_nonneg_right _ hW.le
    exact le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) hn.le)
  · change ‖n⁻¹*W⁻¹*fderiv ℝ (F ∘ normalWaveEquiv) x (Pi.single i 1)‖ ≤
      (|U q|+Real.sqrt (coordinateGradientPair g U U q)/n)/W
    simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hW),abs_of_pos (inv_pos.mpr hn)]
    calc
      _ ≤ n⁻¹*W⁻¹*Real.sqrt (coordinateGradientPair g U U q) :=
        mul_le_mul_of_nonneg_left (hder i) (by positivity)
      _ = (Real.sqrt (coordinateGradientPair g U U q)/n)/W := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg _)) hW.le

lemma realWaveJet_to_intrinsic_lower {U : Sphere 3 → ℝ}
    (hU : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ U)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (p : Sphere 3)
    {n W : ℝ} (hn : 0 < n) (hW : 0 < W) (x : Fin 3 → ℝ) (B : ℕ)
    (hmetric : ∀ v : Euclidean 3,
      selfMetricFlat (sphereChartMetric g p) (normalWaveEquiv x) v v ≤ ‖v‖^2)
    (hjet : 1/n^B ≤ ‖realWaveJet n W
      ((U ∘ (chartAt (Euclidean 3) p).symm) ∘ normalWaveEquiv) x‖) :
    W/n^B ≤ |U ((chartAt (Euclidean 3) p).symm (normalWaveEquiv x))|+
        Real.sqrt (coordinateGradientPair g U U ((chartAt (Euclidean 3) p).symm
          (normalWaveEquiv x)))/n := by
  have hh := (le_div_iff₀ hW).mp (hjet.trans (realWaveJet_intrinsic_upper hU g p hn hW x hmetric))
  simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hh


end


section
open Set Filter Manifold
open scoped Topology ContDiff

lemma sphericalWeight_pos (φ : Sphere 3 → ℝ) (n : ℕ) (q : Sphere 3) :
    0 < sphericalWeight φ n q := add_pos_of_pos_of_nonneg (Real.exp_pos _) (by positivity)

lemma spherical_inner_is_exceptional {φ : Sphere 3 → ℝ} {t : ℝ}
    (hgap : ∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
      sphericalRadius sourceAxisOne sourceAxisTwo q < t →
      Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q)
    {n : ℕ} (hn : 1 ≤ n) {q : Sphere 3}
    (hq : sphericalRadius sourceAxisOne sourceAxisTwo q < t) :
    ‖planarLinear sourceAxisOne sourceAxisTwo q‖^n ≤
      (n:ℝ)^6*Real.exp ((n:ℝ)*φ q) := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hr := sphericalRadius_nonneg sourceAxisOne sourceAxisTwo q
  rw [←sphericalRadius_eq_planar_norm]
  have hbase : sphericalRadius sourceAxisOne sourceAxisTwo q ≤ Real.exp (φ q) := by
    by_cases hz : sphericalRadius sourceAxisOne sourceAxisTwo q=0
    · rw [hz]; exact (Real.exp_pos _).le
    · have hr0 : 0 < sphericalRadius sourceAxisOne sourceAxisTwo q := lt_of_le_of_ne hr (Ne.symm hz)
      have hh := Real.exp_lt_exp.mpr (hgap q hr0 hq)
      rw [Real.exp_log hr0] at hh
      exact hh.le
  calc
    _ ≤ (Real.exp (φ q))^n := pow_le_pow_left₀ hr hbase n
    _ = Real.exp ((n:ℝ)*φ q) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ hnR)

theorem spherical_global_jet_lower_oai
    (g g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {φ : Sphere 3 → ℝ} {t : ℝ}
    (hin : ∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
      sphericalRadius sourceAxisOne sourceAxisTwo q < t →
      Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q)
    {F : Set (Sphere 3)} (hF : F ⊆ {q | sphericalRadius sourceAxisOne sourceAxisTwo q < t})
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    {n : ℕ} (hn : 2 ≤ n) (C : ℝ) (hnC : 2*C ≤ (n:ℝ)^2)
    (hcover : ∀ q : Sphere 3, ‖planarLinear sourceAxisOne sourceAxisTwo q‖^n ≤
      (n:ℝ)^6*Real.exp ((n:ℝ)*φ q) → sphericalRadius sourceAxisOne sourceAxisTwo q ≤ 3/10)
    {u : Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hsmall : ∀ q : Sphere 3, |sphericalWaveLift u q|+
      ‖fderiv ℝ (sphericalWaveLift u ∘ (chartAt (Euclidean 3) q).symm) 0‖/(n:ℝ) ≤
        C*(n:ℝ)^4*Real.exp ((n:ℝ)*φ q))
    (hjet : ∀ y ∈ sphericalExceptionalInChart φ n,
      1/(n:ℝ)^110 ≤ ‖realWaveJet n (sphericalChartWeight φ n y)
        (((roundPower sourceAxisOne sourceAxisTwo n ∘
          (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) y‖) :
    ∀ q : Sphere 3, sphericalWeight φ n q/(n:ℝ)^110 ≤
      |(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q|+
      Real.sqrt (coordinateGradientPair g
        (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u)
        (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q)/(n:ℝ) := by
  let U := roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u
  have hU : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ U :=
    (roundPower_smooth _ _ _).add (sphericalWaveLift_smooth hu hc)
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  intro q
  by_cases hE : ‖planarLinear sourceAxisOne sourceAxisTwo q‖^n ≤ (n:ℝ)^6*Real.exp ((n:ℝ)*φ q)
  · have hq := hcover q hE
    have hqs := sphericalRadius_sublevel_in_source sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole (by norm_num : (3/10:ℝ)<1) hq
    let x := normalWaveEquiv.symm (chartAt (Euclidean 3) sourcePole q)
    have hx : normalWaveEquiv x=chartAt (Euclidean 3) sourcePole q := normalWaveEquiv.apply_symm_apply _
    have hqx : (chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv x)=q := by
      rw [hx,(chartAt (Euclidean 3) sourcePole).left_inv hqs]
    have hW : sphericalChartWeight φ n x=sphericalWeight φ n q := by
      simp only [sphericalChartWeight,sphericalWeight,roundPlanarChart,hqx]
    have hxE : x ∈ sphericalExceptionalInChart φ n := by
      simpa only [sphericalExceptionalInChart,mem_ofPred_eq,roundPlanarChart,Function.comp_apply,hqx] using hE
    have he : U ∘ (chartAt (Euclidean 3) sourcePole).symm=
        (roundPower sourceAxisOne sourceAxisTwo n ∘ (chartAt (Euclidean 3) sourcePole).symm)+u := by
      funext y
      simp only [U,Function.comp_apply,Pi.add_apply,sphericalWaveLift_apply]
    have hlow := realWaveJet_to_intrinsic_lower hU g sourcePole hn0
      (hW.symm ▸ sphericalWeight_pos φ n q) x 110
      (hmetric _ (by rw [hx]; exact ⟨q,hq,rfl⟩))
      (by rw [he]; exact hjet x hxE)
    simpa only [hW,hqx] using hlow
  · have hqF : q ∉ F := fun hq => hE (spherical_inner_is_exceptional hin hn1 (hF hq))
    have hround : ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
        g.inner q v w=(inner ℝ : Euclidean 4 → Euclidean 4 → ℝ)
          (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4) (fun p : Sphere 3 => (p:Euclidean 4)) q v)
          (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4) (fun p : Sphere 3 => (p:Euclidean 4)) q w) :=
      fun v w => (hext q hqF v w).trans (hg₀ q v w)
    have hlow := roundPower_dominant_perturbation_jet_lower sourceAxisOne sourceAxisTwo n hn1
      source_axes_orthonormal.1 source_axes_orthonormal.2.1 source_axes_orthonormal.2.2
      q (sphericalWaveLift u) (sphericalWaveLift_smooth hu hc) (φ q) C hnC (le_of_not_ge hE) (hsmall q)
    have hn2 : (2:ℝ)≤n := by exact_mod_cast hn
    have hfour : (4:ℝ)≤(n:ℝ)^110 := by
      calc
        _ ≤ (n:ℝ)^2 := by nlinarith
        _ ≤ _ := pow_le_pow_right₀ (by linarith : (1:ℝ)≤n) (by omega : 2≤110)
    rw [round_centered_gradient_norm g q U hround]
    exact (div_le_div_of_nonneg_left (sphericalWeight_pos φ n q).le (by norm_num : (0:ℝ)<4) hfour).trans hlow

end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.spherical_global_jet_lower_oai := @OAI.YauCounterexamples.spherical_global_jet_lower_oai
