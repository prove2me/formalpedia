-- Prove2me | solution 1 for OAI.YauCounterexamples.three_clean_collar_gradient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:34:38.689748+00:00
-- url     : https://prove2.me/submissions/349aa840-cac8-4855-a15f-a2d6570ee542

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_threeCoupled_gradient_value

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateGradientPairCongrNhds
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
section LocalPair
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma coordinateGradientPair_congr_nhds (g : SmoothMetric E M) {u v : M → ℝ} {x : M}
    (he : u =ᶠ[𝓝 x] v) : coordinateGradientPair g u u x = coordinateGradientPair g v v x := by
  let c := chartAt E x
  have hx : c x ∈ c.target := c.map_source (mem_chart_source _ _)
  have ht : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv (mem_chart_source _ _)] using (c.continuousAt_symm hx).tendsto
  have hd : fderiv ℝ (u ∘ c.symm) (c x) = fderiv ℝ (v ∘ c.symm) (c x) :=
    (he.comp_tendsto ht).fderiv_eq
  dsimp only [c] at hd
  simp only [coordinateGradientPair,hd]
end LocalPair



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
lemma threeNormalInv_continuous : Continuous threeNormalInv :=
  (continuousOn_univ.mp (by simpa only [three_chart_target] using (chartAt ThreeModel threeProfileCenter).continuousOn_symm)).comp threeNormalEquiv.continuous
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


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
lemma threeNormalInv_closedBall_closed (r : ℝ) : IsClosed (threeNormalInv '' closedBall 0 r) :=
  ((isCompact_closedBall (0:NormalWaveSpace) r).image threeNormalInv_continuous).isClosed
end


open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

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
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions ENNReal NNReal
lemma three_exterior_profile_pair
    (g : SmoothMetric ThreeModel ThreeManifold) {b : ℝ} (he : ThreeExterior g b)
    (k : ℕ) (u : ThreeManifold → ℝ)
    (hu : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius k q)
    {q : ThreeManifold} (hq : q∉threeNormalInv '' closedBall 0 b) :
    coordinateGradientPair g u u q=coordinateGradientPair threeBackgroundMetric
      (threeCoupled threeCouplingRadius k) (threeCoupled threeCouplingRadius k) q := by
  have hgerm : u =ᶠ[𝓝 q] threeCoupled threeCouplingRadius k := by
    filter_upwards [(threeNormalInv_closedBall_closed b).isOpen_compl.mem_nhds hq] with z hz
    exact hu z hz
  rw [coordinateGradientPair_congr_nhds g hgerm]
  exact coordinateGradientPair_metric_point_eq g threeBackgroundMetric q
    (fun v w => congrArg (fun T => T v w) (he q hq)) _ _
lemma three_clean_collar_gradient_oai
    (g : SmoothMetric ThreeModel ThreeManifold) {R b c : ℝ} (hR : 0<R)
    (hclean : ThreeCleanBall R) (hc : c<R/2) (he : ThreeExterior g b)
    (k : ℕ) (hk : 1 ≤ k) (u : ThreeManifold → ℝ)
    (hu : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius k q) :
    ∀ q∈threeCollar b c, 0 < coordinateGradientPair g u u q := by
  intro q hq
  obtain ⟨y,hy,rfl⟩ := hq.1
  obtain ⟨hl,hr⟩ := hclean y (closedBall_subset_closedBall (by linarith : c ≤ R) (ball_subset_closedBall hy))
  rw [three_exterior_profile_pair g he k u hu hq.2]
  apply lt_of_lt_of_le _ (threeCoupled_clean_gradient_lower k hk _ hl hr)
  have hp : (0:ℝ)<‖productA (threeNormalInv y).1‖ := by linarith
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  positivity
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.three_clean_collar_gradient_oai := @OAI.YauCounterexamples.three_clean_collar_gradient_oai
