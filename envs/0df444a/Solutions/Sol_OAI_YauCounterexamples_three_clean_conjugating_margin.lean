-- Prove2me | solution 1 for OAI.YauCounterexamples.three_clean_conjugating_margin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:35:22.904765+00:00
-- url     : https://prove2.me/submissions/30f010f9-f588-442e-8a34-09de941c72e6

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_threeCoupled_gradient_value

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

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeCutoffControlBounds
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
lemma three_clean_conjugating_margin_oai (g : SmoothMetric ThreeModel ThreeManifold)
    (p : ThreeManifold) (hg : ∀ v z : TangentSpace 𝓘(ℝ,ThreeModel) p,
      g.inner p v z=threeBackgroundMetric.inner p v z)
    (k : ℕ) (hk : 1 ≤ k) (hρ : 1/2 ≤ ‖productA p.1‖) (hρu : ‖productA p.1‖ ≤ 3/4)
    (w : ThreeManifold → ℝ) (hwl : 1/2 ≤ w p)
    (hGw : coordinateGradientPair g w w p ≤ 1/4096) :
    (threeCoupled threeCouplingRadius k p)^2*coordinateGradientPair g w w p <
      (w p)^2*coordinateGradientPair g (threeCoupled threeCouplingRadius k) (threeCoupled threeCouplingRadius k) p := by
  let W := ‖productA p.1‖^k
  have hW : 0<W := pow_pos ((by norm_num : (0:ℝ)<1/2).trans_le hρ) k
  have hlower := threeCoupled_clean_gradient_lower k hk p hρ hρu
  rw [←coordinateGradientPair_metric_point_eq g threeBackgroundMetric p hg] at hlower
  have hU := threeCoupled_clean_abs k p hρ
  have hUp : (threeCoupled threeCouplingRadius k p)^2≤4*W^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤2*W)).mpr hU
    rw [sq_abs] at hh; nlinarith
  have hwl2 : 1/4≤(w p)^2 := by nlinarith
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hK : W^2≤((k:ℝ)*W)^2 := by nlinarith [mul_le_mul_of_nonneg_right hkR hW.le]
  have hsm := mul_le_mul hUp hGw (coordinateGradientPair_nonneg g w p) (by positivity : 0≤4*W^2)
  have hl := mul_le_mul hwl2 hlower (by positivity : 0≤(1/32:ℝ)*((k:ℝ)*W)^2) (sq_nonneg (w p))
  nlinarith [sq_pos_of_pos hW]
end


open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.three_clean_conjugating_margin_oai := @OAI.YauCounterexamples.three_clean_conjugating_margin_oai
