-- Prove2me | solution 1 for OAI.YauCounterexamples.threeCoupled_conjugate_gradient_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:26:01.467748+00:00
-- url     : https://prove2.me/submissions/49e686ce-991e-4fed-9034-f374d048bef6

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_threeCoupled_gradient_value

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

end GradientPairCalculus

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
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_mul_left {f u : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (v : M → ℝ) (g : SmoothMetric E M) (x : M) :
    coordinateGradientPair g (fun y => f y * u y) v x =
      f x * coordinateGradientPair g u v x + u x * coordinateGradientPair g f v x := by
  let c := chartAt E x
  have hx := c.map_source (mem_chart_source E x)
  have hf' := (contDiffAt_inChart hf x hx).differentiableAt (by simp)
  have hu' := (contDiffAt_inChart hu x hx).differentiableAt (by simp)
  have he : ((fun y => f y * u y) ∘ c.symm) =
      fun y => (f ∘ c.symm) y * (u ∘ c.symm) y := rfl
  unfold coordinateGradientPair
  change (∑ i, ∑ j, _ * fderiv ℝ ((fun y => f y * u y) ∘ c.symm) (c x) _ * _) = _
  rw [he]
  erw [fderiv_fun_mul hf' hu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    Function.comp_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [c]
  rw [(chartAt E x).left_inv (mem_chart_source E x)]
  ring



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
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ScalarCauchyCross
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
open Set Filter
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma coordinateGradientPair_cauchy (g : SmoothMetric E M) (u v : M → ℝ) (x : M) :
    coordinateGradientPair g u v x ^ 2 ≤
      coordinateGradientPair g u u x * coordinateGradientPair g v v x := by
  let c := chartAt E x
  let a := (metricCoefficients g x (c x))⁻¹
  let du := fun i => fderiv ℝ (u ∘ c.symm) (c x) (Module.finBasis ℝ E i)
  let dv := fun i => fderiv ℝ (v ∘ c.symm) (c x) (Module.finBasis ℝ E i)
  have hp := (metricCoefficients_posDef g x (c.map_source (mem_chart_source E x))).inv
  have he (f h : M → ℝ) : coordinateGradientPair g f h x =
      (fun i => fderiv ℝ (f ∘ c.symm) (c x) (Module.finBasis ℝ E i)) ⬝ᵥ
        (a *ᵥ (fun i => fderiv ℝ (h ∘ c.symm) (c x) (Module.finBasis ℝ E i))) := by
    simp only [coordinateGradientPair,dotProduct,Matrix.mulVec,Finset.mul_sum,a,c]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he u v,he u u,he v v]
  exact real_matrix_cauchy hp.posSemidef du dv

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

lemma scalar_cauchy_cross {a b c X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hc : c^2 ≤ X*Y) : 2*a*b*c ≤ a^2*X+b^2*Y := by
  have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg (a*b))
  apply le_of_sq_le_sq _ (by positivity)
  nlinarith [sq_nonneg (a^2*X-b^2*Y)]

lemma coordinateGradientPair_mul_self_le {E M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    {f u : M → ℝ} (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (g : SmoothMetric E M) (x : M) :
    coordinateGradientPair g (fun y => f y*u y) (fun y => f y*u y) x ≤
      2*(f x)^2*coordinateGradientPair g u u x + 2*(u x)^2*coordinateGradientPair g f f x := by
  have hc := scalar_cauchy_cross (a:=f x) (b:=u x)
    (coordinateGradientPair_nonneg g u x) (coordinateGradientPair_nonneg g f x)
    (coordinateGradientPair_cauchy g u f x)
  rw [coordinateGradientPair_mul_left hf hu,
    coordinateGradientPair_symm g u (fun y => f y*u y) x,
    coordinateGradientPair_symm g f (fun y => f y*u y) x,
    coordinateGradientPair_mul_left hf hu,
    coordinateGradientPair_mul_left hf hu,
    coordinateGradientPair_symm g f u x]
  nlinarith


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
local instance threeModelContinuousSMul'_r1e108c_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.threeAmbientNormedSpace'
local instance threeAmbientContinuousSMul'_r1e108c_1 : ContinuousSMul ℝ ThreeAmbient := inferInstance
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
lemma productAxis_coord (i : Fin 3) (x : Euclidean 3) : inner ℝ (productAxis i) x = x i := by
  simp [productAxis,EuclideanSpace.inner_single_left]
lemma productA_re (x : Euclidean 3) : (productA x).re=x 0 := by simp [productA,planarLinear,productAxis_coord]
lemma productA_im (x : Euclidean 3) : (productA x).im=x 1 := by simp [productA,planarLinear,productAxis_coord]
lemma productB_re (x : Euclidean 3) : (productB x).re=x 0 := by simp [productB,planarLinear,productAxis_coord]
lemma productB_im (x : Euclidean 3) : (productB x).im=x 2 := by simp [productB,planarLinear,productAxis_coord]
lemma threeCoupled_eq (r : ℝ) (k : ℕ) : threeCoupled r k =
    fun p => threePower (productAxis 0) (productAxis 1) k p+r^k*threePower (productAxis 0) (productAxis 2) k p := by
  funext p
  simp only [threeCoupled,threeCoupledComplex,add_mul,mul_assoc,Complex.add_re,
    ←Complex.ofReal_pow,Complex.re_ofReal_mul,threePower,threeComplexPower,productA,productB]
attribute [local instance] OAI.YauCounterexamples.threeCoupledNormedSpace
local instance threeCoupledContinuousSMul_r1e108c_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeCoupled_smooth (r : ℝ) (k : ℕ) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeCoupled r k) := by
  rw [threeCoupled_eq]
  exact (threePower_smooth _ _ _).add (contMDiff_const.mul (threePower_smooth _ _ _))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ThreeNoncancelNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
lemma productSphere_norm_sq (p : Sphere 2) : (p:Euclidean 3) 0^2+(p:Euclidean 3) 1^2+(p:Euclidean 3) 2^2=1 := by
  have hn : ‖(p:Euclidean 3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.property
  have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (p:Euclidean 3)
  simpa [hn,Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs,add_assoc] using hh.symm
lemma productA_norm_le (p : Sphere 2) : ‖productA p‖≤1 := by
  have hh := productSphere_norm_sq p
  have hn := Complex.normSq_eq_norm_sq (productA p)
  simp only [Complex.normSq_apply,productA_re,productA_im] at hn
  nlinarith [sq_nonneg ((p:Euclidean 3) 2),norm_nonneg (productA p)]
lemma productB_norm_le (p : Sphere 2) : ‖productB p‖≤1 := by
  have hh := productSphere_norm_sq p
  have hn := Complex.normSq_eq_norm_sq (productB p)
  simp only [Complex.normSq_apply,productB_re,productB_im] at hn
  nlinarith [sq_nonneg ((p:Euclidean 3) 1),norm_nonneg (productB p)]

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ThreeProjectionNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
lemma complex_re_sq_le_norm_sq (z : ℂ) : z.re^2 ≤ ‖z‖^2 := by
  have hn := Complex.normSq_eq_norm_sq z
  simp only [Complex.normSq_apply] at hn
  nlinarith [sq_nonneg z.im]
lemma complex_clean_energy_lower (C D A B : ℂ) (hA : ‖A‖ ≤ 3/4) (hB : ‖B‖ ≤ 1)
    (hD : ‖D‖ ≤ ‖C‖/100) (s : ℝ) :
    (1/32:ℝ)*‖C‖^2 ≤ (C.re+D.re)^2+C.im^2+D.im^2-(C*A+D*B).re^2+s^2 := by
  have hC := Complex.normSq_eq_norm_sq C
  have hDq := Complex.normSq_eq_norm_sq D
  simp only [Complex.normSq_apply] at hC hDq
  have hAs : ‖A‖^2≤(3/4:ℝ)^2 := sq_le_sq₀ (norm_nonneg _) (by norm_num) |>.mpr hA
  have hBs : ‖B‖^2≤1 := by nlinarith [norm_nonneg B]
  have hDs : ‖D‖^2≤‖C‖^2/10000 := by
    have hh := (sq_le_sq₀ (norm_nonneg D) (by positivity : 0≤‖C‖/100)).mpr hD
    nlinarith
  have hCA := complex_re_sq_le_norm_sq (C*A)
  have hDB := complex_re_sq_le_norm_sq (D*B)
  rw [norm_mul,mul_pow] at hCA hDB
  have hCA' : (C*A).re^2≤(9/16:ℝ)*‖C‖^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hAs (sq_nonneg ‖C‖)]
  have hDB' : (D*B).re^2≤‖D‖^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hBs (sq_nonneg ‖D‖)]
  have hc : (C.re+D.re)^2+C.im^2+D.im^2≥(3/4:ℝ)*‖C‖^2-3*‖D‖^2 := by
    nlinarith [sq_nonneg (C.re/2+2*D.re),sq_nonneg C.im,sq_nonneg D.im]
  have hu : (C*A+D*B).re^2≤(45/64:ℝ)*‖C‖^2+5*‖D‖^2 := by
    rw [Complex.add_re]
    nlinarith [sq_nonneg ((C*A).re/2-2*(D*B).re)]
  nlinarith [sq_nonneg s,sq_nonneg ‖C‖]
lemma threeCoupled_clean_gradient_lower (k : ℕ) (hk : 1 ≤ k) (p : ThreeManifold)
    (hρ : 1/2 ≤ ‖productA p.1‖) (hρu : ‖productA p.1‖ ≤ 3/4) :
    (1/32:ℝ)*((k:ℝ)*‖productA p.1‖^k)^2 ≤
      coordinateGradientPair threeBackgroundMetric (threeCoupled threeCouplingRadius k)
        (threeCoupled threeCouplingRadius k) p := by
  let C := (p.2:ℂ)^k*productA p.1^(k-1)
  let D := (p.2:ℂ)^k*(threeCouplingRadius:ℂ)^k*productB p.1^(k-1)
  have hCn : ‖C‖=‖productA p.1‖^(k-1) := by simp [C,norm_pow,Circle.norm_coe]
  have hDn : ‖D‖≤‖C‖/100 := by
    have hr : 0≤threeCouplingRadius := by norm_num [threeCouplingRadius]
    have hrρ : threeCouplingRadius≤‖productA p.1‖ := by norm_num [threeCouplingRadius] at *; linarith
    have hB := pow_le_pow_left₀ (norm_nonneg (productB p.1)) (productB_norm_le p.1) (k-1)
    rw [one_pow] at hB
    have hDr : ‖D‖≤threeCouplingRadius^k := by
      simp only [D,norm_mul,norm_pow,Circle.norm_coe,one_pow,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
      exact mul_le_of_le_one_right (pow_nonneg hr _) hB
    calc
      _ ≤ threeCouplingRadius^k := hDr
      _ = threeCouplingRadius*threeCouplingRadius^(k-1) := by rw [←pow_succ',Nat.sub_add_cancel hk]
      _ ≤ threeCouplingRadius*‖productA p.1‖^(k-1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrρ _) hr
      _ = ‖C‖/100 := by rw [hCn]; norm_num [threeCouplingRadius]; ring
  have hp (z : ℂ) : z^(k-1)*z=z^k := by rw [←pow_succ,Nat.sub_add_cancel hk]
  have he : C*productA p.1+D*productB p.1=threeCoupledComplex threeCouplingRadius k p := by
    dsimp only [C,D,threeCoupledComplex]
    rw [←hp (productA p.1),←hp (productB p.1)]
    ring
  have hl := complex_clean_energy_lower C D (productA p.1) (productB p.1) hρu (productB_norm_le p.1) hDn
    (threeCoupledComplex threeCouplingRadius k p).im
  rw [he] at hl
  have hstep : ‖productA p.1‖^k ≤ ‖C‖ := by
    rw [hCn,show k=(k-1)+1 by omega,pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (productA_norm_le p.1)
  have hstepsq := (sq_le_sq₀ (pow_nonneg (norm_nonneg _) _) (norm_nonneg C)).mpr hstep
  rw [threeCoupled_gradient_value _ k hk]
  change _ ≤ (k:ℝ)^2*((C.re+D.re)^2+C.im^2+D.im^2-(threeCoupledComplex threeCouplingRadius k p).re^2+
    (threeCoupledComplex threeCouplingRadius k p).im^2)
  have hh := mul_le_mul_of_nonneg_left hl (sq_nonneg (k:ℝ))
  have hs := mul_le_mul_of_nonneg_left hstepsq (sq_nonneg (k:ℝ))
  nlinarith
end


open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
lemma coordinateGradientPair_metric_point_eq {E M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (g h : SmoothMetric E M) (p : M)
    (he : ∀ v w : TangentSpace 𝓘(ℝ,E) p, g.inner p v w=h.inner p v w)
    (u v : M → ℝ) : coordinateGradientPair g u v p=coordinateGradientPair h u v p := by
  have hp := (chartAt E p).left_inv (mem_chart_source E p)
  have hm : metricCoefficients g p ((chartAt E p) p)=metricCoefficients h p ((chartAt E p) p) := by
    unfold metricCoefficients
    have hh : ∀ q, q=p → ∀ a b : TangentSpace 𝓘(ℝ,E) q, g.inner q a b=h.inner q a b := by
      intro q hq; subst q; exact he
    funext i j
    exact hh _ hp _ _
  simp only [coordinateGradientPair,hm]
lemma threeCoupled_clean_abs (k : ℕ) (p : ThreeManifold) (hρ : 1/2≤‖productA p.1‖) :
    |threeCoupled threeCouplingRadius k p|≤2*‖productA p.1‖^k := by
  have hr : 0≤threeCouplingRadius := by norm_num [threeCouplingRadius]
  have hB : threeCouplingRadius*‖productB p.1‖≤‖productA p.1‖ := by
    have hb := mul_le_mul_of_nonneg_left (productB_norm_le p.1) hr
    norm_num [threeCouplingRadius] at hb
    norm_num [threeCouplingRadius]
    linarith
  have he := Complex.abs_re_le_norm (threeCoupledComplex threeCouplingRadius k p)
  change |threeCoupled threeCouplingRadius k p|≤_ at he
  have hn : ‖threeCoupledComplex threeCouplingRadius k p‖≤2*‖productA p.1‖^k := by
    unfold threeCoupledComplex
    rw [norm_mul,norm_pow,Circle.norm_coe,one_pow,mul_one]
    have hh := norm_add_le (productA p.1^k) ((threeCouplingRadius:ℂ)^k*productB p.1^k)
    simp only [norm_pow,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,←mul_pow] at hh
    have hpow := pow_le_pow_left₀ (mul_nonneg hr (norm_nonneg _)) hB k
    simp only [mul_pow] at hh hpow
    linarith
  exact he.trans hn
attribute [local instance] OAI.YauCounterexamples.threeProjectionNormedSpace
local instance threeProjectionContinuousSMul_r1e108c_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeCoupled_conjugate_gradient_lower_oai
    (g : SmoothMetric ThreeModel ThreeManifold) (p : ThreeManifold)
    (hg : ∀ v z : TangentSpace 𝓘(ℝ,ThreeModel) p,
      g.inner p v z=threeBackgroundMetric.inner p v z)
    (k : ℕ) (hk : 1≤k) (hρ : 1/2≤‖productA p.1‖) (hρu : ‖productA p.1‖≤3/4)
    (w : ThreeManifold → ℝ) (hw : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ w)
    (hw0 : ∀ x, w x≠0) (hwl : 1/2≤w p) (hwu : w p≤2)
    (hGw : coordinateGradientPair g w w p≤1/4096) :
    (1/1024:ℝ)*((k:ℝ)*‖productA p.1‖^k)^2≤
      coordinateGradientPair g (fun x => threeCoupled threeCouplingRadius k x/w x)
        (fun x => threeCoupled threeCouplingRadius k x/w x) p := by
  let U := threeCoupled threeCouplingRadius k
  let u := fun x => U x/w x
  let W := ‖productA p.1‖^k
  have hu := (threeCoupled_smooth threeCouplingRadius k).div₀ hw hw0
  have he : U=fun x => w x*u x := by funext x; dsimp [u]; field_simp [hw0 x]
  have hl := threeCoupled_clean_gradient_lower k hk p hρ hρu
  rw [←coordinateGradientPair_metric_point_eq g threeBackgroundMetric p hg] at hl
  have hupper := coordinateGradientPair_mul_self_le hw hu g p
  change coordinateGradientPair g (fun y => w y*u y) (fun y => w y*u y) p≤_ at hupper
  rw [←he] at hupper
  have hU := threeCoupled_clean_abs k p hρ
  change |U p|≤2*W at hU
  have hUp : (U p)^2≤4*W^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (U p)) (by dsimp [W]; positivity : 0≤2*W)).mpr hU
    rw [sq_abs] at hh; nlinarith
  have hwl2 : 1/4≤(w p)^2 := by nlinarith
  have hwu2 : (w p)^2≤4 := by nlinarith
  have hu2 : (u p)^2≤16*W^2 := by
    have hh := mul_le_mul_of_nonneg_right hwl2 (sq_nonneg (u p))
    have heq := congrFun he p
    rw [heq,mul_pow] at hUp
    nlinarith
  have hGu := coordinateGradientPair_nonneg g u p
  have hGwn := coordinateGradientPair_nonneg g w p
  have hsmall := mul_le_mul hu2 hGw hGwn (by positivity : 0≤16*W^2)
  have hlarge := mul_le_mul_of_nonneg_right hwu2 hGu
  have hk2 : 1≤(k:ℝ)^2 := by
    have hh : (1:ℝ)≤k := by exact_mod_cast hk
    nlinarith
  have hfreq := mul_le_mul_of_nonneg_right hk2 (sq_nonneg W)
  change (1/32:ℝ)*((k:ℝ)*W)^2 ≤ coordinateGradientPair g U U p at hl
  change coordinateGradientPair g U U p≤2*(w p)^2*coordinateGradientPair g u u p+2*(u p)^2*coordinateGradientPair g w w p at hupper
  change (1/1024:ℝ)*((k:ℝ)*W)^2 ≤ coordinateGradientPair g u u p
  nlinarith

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.threeCoupled_conjugate_gradient_lower_oai := @OAI.YauCounterexamples.threeCoupled_conjugate_gradient_lower_oai
