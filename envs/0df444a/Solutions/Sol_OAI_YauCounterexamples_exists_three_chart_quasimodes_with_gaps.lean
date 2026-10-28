-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_three_chart_quasimodes_with_gaps
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:13:31.075367+00:00
-- url     : https://prove2.me/submissions/2a5b55ae-4f36-4381-b382-6c224323e67c

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_exists_supported_box_nodal_quasimodes_subregions
import Theorems.Thm_OAI_YauCounterexamples_exists_three_robust_global_profile_family
import Theorems.Thm_OAI_YauCounterexamples_threePacket_background_input_bounds

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

end


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ProductSphereFstContraction
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
lemma complexIdentityPlanar (z : ℂ) : planarLinear (1:ℂ) Complex.I z = z := by
  apply Complex.ext <;> simp [planarLinear_apply,Complex.inner,Complex.mul_re,Complex.mul_im]
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ProductSphereFstPower
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
  {n m : ℕ} [Fact (Module.finrank ℝ A = n+1)] [Fact (Module.finrank ℝ B = m+1)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ A] in
lemma productSphere_fstPower_smooth (p : Metric.sphere (0:A) 1) (ℓ : A →L[ℝ] ℂ) (k : ℕ) :
    ContDiff ℝ ∞ (productSphere_fstPower (n:=n) (m:=m) p ℓ k) :=
  ((ℓ.contDiff.comp (roundChart_smooth _ _)).pow k).comp
    (WithLp.fstL 2 ℝ (Euclidean n) (Euclidean m)).contDiff
omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_smooth (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ) (k : ℕ) :
    ContDiff ℝ ∞ (productSphere_sndPower (n:=n) (m:=m) p ℓ k) :=
  ((ℓ.contDiff.comp (roundChart_smooth _ _)).pow k).comp
    (WithLp.sndL 2 ℝ (Euclidean n) (Euclidean m)).contDiff
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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

lemma selfMetricFlat_invertible (g : SmoothMetric E E) (x : E) :
    (selfMetricFlat g x).IsInvertible := by
  rw [←localMetricFlat_self g x x]
  exact localMetricFlat_invertible g x x (mem_baseSet_trivializationAt E _ x)


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
open Set Filter
open scoped Topology InnerProductSpace
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

lemma coordinateMetricGradient_eq_zero_iff (g : SmoothMetric E E) (f : E → ℝ) (x : E) :
    coordinateMetricGradient g f x = 0 ↔ fderiv ℝ f x = 0 := by
  constructor
  · intro h
    have hh := (selfMetricFlat_invertible g x).inverse_apply_eq.mp h
    simpa only [map_zero] using hh
  · intro h
    simp only [coordinateMetricGradient,h,map_zero]


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
lemma three_chart_symm (p : ThreeManifold) :
    threeImmersion ∘ (chartAt ThreeModel p).symm = threeChartMap p := by
  funext y
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · change ((chartAt (Euclidean 2) p.1).symm y.fst : Euclidean 3) = _
    exact congrFun (sphere_chart_symm p.1) y.fst
  · change ((chartAt (Euclidean 1) p.2).symm y.snd : ℂ) = _
    exact congrFun (unitSphere_chart_symm (n:=1) p.2) y.snd
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
attribute [local instance] OAI.YauCounterexamples.sphereN_dimension_fact
lemma threeComplexPower_chart (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) :
    threeComplexPower a b k ∘ (chartAt ThreeModel p).symm =
      fun z => productSphere_fstPower (n:=2) (m:=1) p.1 (planarLinear a b) k z*
        productSphere_sndPower (n:=2) (m:=1) p.2 (planarLinear (1:ℂ) Complex.I) k z := by
  funext y
  have hh := congrFun (three_chart_symm p) y
  have h₁ := congrArg (fun q : ThreeAmbient => q.fst) hh
  have h₂ := congrArg (fun q : ThreeAmbient => q.snd) hh
  change (((chartAt ThreeModel p).symm y).1:Euclidean 3) =
    roundChart (p.1:Euclidean 3) (sphereFrame p.1) y.fst at h₁
  change (((chartAt ThreeModel p).symm y).2:ℂ) =
    roundChart (p.2:ℂ) (unitSphereFrame (n:=1) p.2) y.snd at h₂
  simp only [Function.comp_apply,threeComplexPower,h₁,h₂]
  simp only [productSphere_fstPower,productSphere_sndPower,Function.comp_apply]
  rw [complexIdentityPlanar]
  rfl
end


section
open Set Filter
open scoped Topology

lemma productFrequency_nonneg (k : ℕ) : 0 ≤ productFrequency k := by
  unfold productFrequency
  positivity
lemma productWaveFrequency_equation (k : ℕ) :
    productWaveFrequency k*(productWaveFrequency k+2)=productFrequency k := by
  have h := Real.sq_sqrt (add_nonneg (productFrequency_nonneg k) zero_le_one)
  unfold productWaveFrequency
  nlinarith
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeFirstNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
attribute [local instance] OAI.YauCounterexamples.threeFirstNormedSpace
local instance threeFirstContinuousSMul_ra022f2_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.sphereFirst_dimension_fact
lemma threeComplexPower_chart_smooth (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) :
    ContDiff ℝ ∞ (threeComplexPower a b k ∘ (chartAt ThreeModel p).symm) := by
  rw [threeComplexPower_chart]
  exact (productSphere_fstPower_smooth _ _ _).mul (productSphere_sndPower_smooth _ _ _)
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
local instance threeCoupledContinuousSMul_ra022f2_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeCoupled_chart_smooth (r : ℝ) (k : ℕ) (p : ThreeManifold) :
    ContDiff ℝ ∞ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) := by
  rw [threeCoupled_eq]
  change ContDiff ℝ ∞ (fun y => (threePower (productAxis 0) (productAxis 1) k ∘ (chartAt ThreeModel p).symm) y +
    r^k*(threePower (productAxis 0) (productAxis 2) k ∘ (chartAt ThreeModel p).symm) y)
  exact (Complex.reCLM.contDiff.comp (threeComplexPower_chart_smooth _ _ _ _)).add
    (contDiff_const.mul (Complex.reCLM.contDiff.comp (threeComplexPower_chart_smooth _ _ _ _)))
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
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeEnvelopeExponent_pos : 0<threeEnvelopeExponent := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
lemma threeEnvelopeExponent_lt : threeEnvelopeExponent<1 := by
  unfold threeEnvelopeExponent
  have h : 1<Real.sqrt 2 := by nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg 2]
  exact (inv_lt_one₀ (lt_trans zero_lt_one h)).mpr h
lemma threeEnvelopeExponent_mul : threeEnvelopeExponent*Real.sqrt 2=1 := by
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))

end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeGlobalRadius_lower (p : ThreeManifold) : (1/200:ℝ) ≤ threeGlobalRadius p := by
  have ha := Complex.normSq_eq_norm_sq (productA p.1)
  have hb := Complex.normSq_eq_norm_sq (productB p.1)
  simp only [Complex.normSq_apply,productA_re,productA_im,productB_re,productB_im] at ha hb
  have hs := productSphere_norm_sq p.1
  by_contra hn
  have hn : threeGlobalRadius p < 1/200 := lt_of_not_ge hn
  have hA := (le_max_left ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)).trans_lt hn
  have hB := (le_max_right ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)).trans_lt hn
  dsimp [threeCouplingRadius] at hB
  have hB' : ‖productB p.1‖<1/2 := by linarith
  have hA' : ‖productA p.1‖<1/2 := by linarith
  nlinarith [norm_nonneg (productA p.1), norm_nonneg (productB p.1),sq_nonneg ((p.1:Euclidean 3) 0)]
lemma threeGlobalRadius_pos (p : ThreeManifold) : 0<threeGlobalRadius p :=
  lt_of_lt_of_le (by norm_num) (threeGlobalRadius_lower p)
lemma threeGlobalRadius_le_one (p : ThreeManifold) : threeGlobalRadius p≤1 := by
  apply max_le (productA_norm_le p.1)
  have hb:=productB_norm_le p.1
  dsimp [threeCouplingRadius]
  nlinarith [norm_nonneg (productB p.1)]
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma productWaveFrequency_scaled_bounds {k : ℕ} (hk : 1≤k) :
    (k:ℝ)-1 ≤ productWaveFrequency k*threeEnvelopeExponent ∧
      productWaveFrequency k*threeEnvelopeExponent ≤ k := by
  have hn : (0:ℝ)≤k := Nat.cast_nonneg _
  have hb := productWaveFrequency_bounds hk
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hp := Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)
  have he := productWaveFrequency_equation k
  dsimp [productFrequency] at he
  have hsK : (Real.sqrt 2*(k:ℝ))^2=2*(k:ℝ)^2 := by rw [mul_pow,hs]
  have hupper : productWaveFrequency k≤Real.sqrt 2*(k:ℝ) := by
    have hv : productWaveFrequency k ^ 2 ≤ 2*(k:ℝ)^2 := by nlinarith [hb.1]
    exact (sq_le_sq₀ (hn.trans hb.1) (mul_nonneg hp.le hn)).mp (by simpa only [hsK] using hv)
  have hlower : Real.sqrt 2*(k:ℝ)≤productWaveFrequency k+1 := by
    have hh := Real.sq_sqrt (add_nonneg (productFrequency_nonneg k) zero_le_one)
    have hz := Real.sqrt_nonneg (productFrequency k+1)
    dsimp [productWaveFrequency,productFrequency] at hh hz ⊢
    nlinarith [sq_nonneg (Real.sqrt (2*(k:ℝ)^2+(k:ℝ)+1)-Real.sqrt 2*(k:ℝ))]
  have hc := threeEnvelopeExponent_pos
  have hc1 := threeEnvelopeExponent_lt
  have hmul := threeEnvelopeExponent_mul
  constructor
  · have hh := mul_le_mul_of_nonneg_right hlower hc.le
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hupper hc.le
    nlinarith

lemma three_radius_pow_eq_exp (p : ThreeManifold) (k : ℕ) :
    threeGlobalRadius p^k=Real.exp ((k:ℝ)*Real.log (threeGlobalRadius p)) := by
  rw [Real.exp_nat_mul,Real.exp_log (threeGlobalRadius_pos p)]

lemma three_positive_envelope_gap (p : ThreeManifold) {k : ℕ} (hk : 1≤k)
    {φ δ : ℝ} (hgap : threeGlobalLog p+δ≤φ) :
    threeGlobalRadius p^k ≤ Real.exp (productWaveFrequency k*(φ-δ)) := by
  have hc := (productWaveFrequency_scaled_bounds hk).2
  have hn := (Nat.cast_nonneg k).trans (productWaveFrequency_bounds hk).1
  have hl := Real.log_nonpos (threeGlobalRadius_pos p).le (threeGlobalRadius_le_one p)
  rw [three_radius_pow_eq_exp]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonpos_right hc hl
  have hg := mul_le_mul_of_nonneg_left hgap hn
  dsimp [threeGlobalLog] at hg
  nlinarith

lemma three_negative_envelope_gap (p : ThreeManifold) {k : ℕ} (hk : 1≤k)
    {φ δ : ℝ} (hδ : 0≤δ) (hgap : φ≤threeGlobalLog p-δ) :
    Real.exp (productWaveFrequency k*φ) ≤
      200*(threeGlobalRadius p)^k*Real.exp (-(k:ℝ)*δ) := by
  have hc := (productWaveFrequency_scaled_bounds hk).1
  have hb := productWaveFrequency_bounds hk
  have hn := (Nat.cast_nonneg k).trans hb.1
  have hl := Real.log_nonpos (threeGlobalRadius_pos p).le (threeGlobalRadius_le_one p)
  have hlb := Real.log_le_log (show (0:ℝ)<1/200 by norm_num) (threeGlobalRadius_lower p)
  have hlog : -Real.log (threeGlobalRadius p) ≤ Real.log 200 := by
    have he : Real.log (1/200:ℝ) = -Real.log 200 := by rw [one_div,Real.log_inv]
    rw [he] at hlb
    linarith
  have hex : productWaveFrequency k*φ ≤ Real.log 200+(k:ℝ)*Real.log (threeGlobalRadius p)-(k:ℝ)*δ := by
    have h1 := mul_le_mul_of_nonpos_right hc hl
    have h2 := mul_le_mul_of_nonneg_left hgap hn
    have h3 := mul_le_mul_of_nonneg_right hb.1 hδ
    dsimp [threeGlobalLog] at h2
    nlinarith
  calc
    _ ≤ Real.exp (Real.log 200+(k:ℝ)*Real.log (threeGlobalRadius p)-(k:ℝ)*δ) := Real.exp_le_exp.mpr hex
    _ = _ := by
      rw [show Real.log 200+(k:ℝ)*Real.log (threeGlobalRadius p)-(k:ℝ)*δ =
        (Real.log 200+(k:ℝ)*Real.log (threeGlobalRadius p))+(-(k:ℝ)*δ) by ring,
        Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<200),←three_radius_pow_eq_exp]
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

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
open Set Filter Function Manifold Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace

lemma threeCoupled_split_powers (r : ℝ) (k : ℕ) (p : ThreeManifold) :
    threeCoupled r k p =
      ((threeComplexPower (productAxis 0) (productAxis 1) 1 p)^k).re+
      (((r:ℂ)*threeComplexPower (productAxis 0) (productAxis 2) 1 p)^k).re := by
  simp only [threeCoupled,threeCoupledComplex,threeComplexPower,pow_one,mul_pow,
    Complex.add_re,add_mul,productA,productB,mul_assoc]

end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

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
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma threePacketA_norm (y : Fin 3 → ℝ) :
    ‖threePacketA y‖=‖productA (threeNormalInv (normalWaveEquiv y)).1‖ := by
  simp only [threePacketA,Function.comp_apply,threeComplexPower,pow_one,norm_mul,Circle.norm_coe,mul_one]
  rfl
lemma threePacketB_norm (y : Fin 3 → ℝ) :
    ‖threePacketB y‖=threeCouplingRadius*‖productB (threeNormalInv (normalWaveEquiv y)).1‖ := by
  simp only [threePacketB,threeComplexPower,pow_one,norm_mul,Circle.norm_coe,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0<threeCouplingRadius by norm_num [threeCouplingRadius])]
  rfl
lemma threePacketWeight_lower (φ : ThreeManifold → ℝ) (k : ℕ) (y : Fin 3 → ℝ) :
    Real.exp (productWaveFrequency k*φ (threeNormalInv (normalWaveEquiv y))) ≤ threePacketWeight φ k y := by
  dsimp [threePacketWeight]
  nlinarith [pow_nonneg (norm_nonneg (threePacketA y)) k,pow_nonneg (norm_nonneg (threePacketB y)) k]
lemma threePacketWeight_upper (φ : ThreeManifold → ℝ) (k : ℕ) (y : Fin 3 → ℝ)
    (hy : y∈threeExceptionalInChart φ k) :
    threePacketWeight φ k y≤(1+(productWaveFrequency k)^6)*
      Real.exp (productWaveFrequency k*φ (threeNormalInv (normalWaveEquiv y))) := by
  dsimp [threeExceptionalInChart] at hy
  dsimp [threePacketWeight]
  nlinarith
lemma threePacket_radius_bound (k : ℕ) (y : Fin 3 → ℝ) :
    threeGlobalRadius (threeNormalInv (normalWaveEquiv y))^k≤‖threePacketA y‖^k+‖threePacketB y‖^k := by
  rw [threePacketA_norm,threePacketB_norm]
  have hr : 0≤threeCouplingRadius := by norm_num [threeCouplingRadius]
  dsimp [threeGlobalRadius]
  rcases le_total ‖productA (threeNormalInv (normalWaveEquiv y)).1‖
    (threeCouplingRadius*‖productB (threeNormalInv (normalWaveEquiv y)).1‖) with h|h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (by positivity)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (by positivity)

lemma threeCoupled_abs_le_radius (k : ℕ) (p : ThreeManifold) :
    |threeCoupled threeCouplingRadius k p|≤2*threeGlobalRadius p^k := by
  rw [threeCoupled_split_powers]
  have hh (i : Fin 3) : ‖threeComplexPower (productAxis 0) (productAxis i) 1 p‖=‖planarLinear (productAxis 0) (productAxis i) p.1‖ := by
    simp [threeComplexPower, Circle.norm_coe]
  have hr : 0≤threeCouplingRadius := by norm_num [threeCouplingRadius]
  have h1 : ‖threeComplexPower (productAxis 0) (productAxis 1) 1 p‖ ≤ threeGlobalRadius p := by
    rw [hh]; exact le_max_left _ _
  have h2 : ‖(threeCouplingRadius:ℂ)*threeComplexPower (productAxis 0) (productAxis 2) 1 p‖≤threeGlobalRadius p := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,hh]
    exact le_max_right _ _
  have hb1 := Complex.abs_re_le_norm ((threeComplexPower (productAxis 0) (productAxis 1) 1 p)^k)
  have hb2 := Complex.abs_re_le_norm (((threeCouplingRadius:ℂ)*threeComplexPower (productAxis 0) (productAxis 2) 1 p)^k)
  rw [norm_pow] at hb1 hb2
  have hp1 := hb1.trans (pow_le_pow_left₀ (norm_nonneg _) h1 k)
  have hp2 := hb2.trans (pow_le_pow_left₀ (norm_nonneg _) h2 k)
  exact (abs_add_le _ _).trans (by linarith)

lemma three_background_sign_small (φ : ThreeManifold → ℝ) {K : Set NormalWaveSpace}
    {δ : ℝ} (hδ : 0<δ) (hgap : ∀ y∈K, threeGlobalLog (threeNormalInv y)+δ≤φ (threeNormalInv y))
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, ∀ y∈K, |threeCoupled threeCouplingRadius k (threeNormalInv y)|≤
      c*Real.exp (productWaveFrequency k*φ (threeNormalInv y)) := by
  let ρ := Real.exp (-δ)
  have hρ : 0<ρ := Real.exp_pos _
  have hρ1 : ρ<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ht : Tendsto (fun k : ℕ => 2*ρ^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul 2
  filter_upwards [eventually_ge_atTop (1:ℕ),ht.eventually (Iio_mem_nhds hc)] with k hk hsmall
  intro y hy
  have hb := productWaveFrequency_bounds hk
  have hrad := three_positive_envelope_gap (threeNormalInv y) hk (hgap y hy)
  have he : Real.exp (productWaveFrequency k*(φ (threeNormalInv y)-δ))≤
      ρ^k*Real.exp (productWaveFrequency k*φ (threeNormalInv y)) := by
    dsimp [ρ]
    rw [←Real.exp_nat_mul,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hb.1 hδ.le]
  calc
    _ ≤ 2*threeGlobalRadius (threeNormalInv y)^k := threeCoupled_abs_le_radius _ _
    _ ≤ 2*(ρ^k*Real.exp (productWaveFrequency k*φ (threeNormalInv y))) := mul_le_mul_of_nonneg_left (hrad.trans he) (by norm_num)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hsmall.le (Real.exp_pos (productWaveFrequency k*φ (threeNormalInv y))).le]

lemma three_exceptional_eventually_coverage (φ : ThreeManifold → ℝ) {K : Set NormalWaveSpace}
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ y∉K, φ (threeNormalInv y)≤threeGlobalLog (threeNormalInv y)-δ) :
    ∀ᶠ k : ℕ in atTop, threeExceptionalInChart φ k⊆normalWaveEquiv.symm '' K := by
  let ρ := Real.exp (-δ)
  have hρ : 0<ρ := Real.exp_pos _
  have hρ1 : ρ<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ht : Tendsto (fun k : ℕ => 12800*((k:ℝ)^6*ρ^k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_const_mul_const_pow_of_lt_one 6 hρ.le hρ1).const_mul 12800
  filter_upwards [eventually_ge_atTop (1:ℕ),ht.eventually (Iio_mem_nhds zero_lt_one)] with k hk hsmall
  intro y hy
  refine ⟨normalWaveEquiv y,?_,normalWaveEquiv.symm_apply_apply y⟩
  by_contra hout
  have hν := productWaveFrequency_bounds hk
  have he := three_negative_envelope_gap (threeNormalInv (normalWaveEquiv y)) hk hδ.le (hgap _ hout)
  have hν0 : 0≤productWaveFrequency k := (Nat.cast_nonneg _).trans hν.1
  have hν6 := pow_le_pow_left₀ hν0 hν.2 6
  have hpos := pow_pos (threeGlobalRadius_pos (threeNormalInv (normalWaveEquiv y))) k
  have hb := (threePacket_radius_bound k y).trans hy
  have hh := hb.trans (mul_le_mul_of_nonneg_left he (pow_nonneg hν0 6))
  have heρ : Real.exp (-(k:ℝ)*δ)=ρ^k := by dsimp [ρ]; rw [←Real.exp_nat_mul]; congr 1; ring
  rw [heρ] at hh
  have hbig : (productWaveFrequency k)^6*(200*threeGlobalRadius (threeNormalInv (normalWaveEquiv y))^k*ρ^k) ≤
      (12800*((k:ℝ)^6*ρ^k))*threeGlobalRadius (threeNormalInv (normalWaveEquiv y))^k := by
    calc
      _ ≤ (2*(k:ℝ))^6*(200*threeGlobalRadius (threeNormalInv (normalWaveEquiv y))^k*ρ^k) :=
        mul_le_mul_of_nonneg_right hν6 (by positivity)
      _ = _ := by ring
  have hbad := hh.trans hbig
  have hs := mul_lt_mul_of_pos_right hsmall hpos
  norm_num at hs
  exact (not_lt_of_ge hbad) hs
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal
lemma threeNormalInv_injective : Function.Injective threeNormalInv := by
  intro x y h
  have hh := congrArg (chartAt ThreeModel threeProfileCenter) h
  dsimp [threeNormalInv,Function.comp_def] at hh
  rw [(chartAt ThreeModel threeProfileCenter).right_inv (by rw [three_chart_target]; trivial),
    (chartAt ThreeModel threeProfileCenter).right_inv (by rw [three_chart_target]; trivial)] at hh
  exact threeNormalEquiv.injective hh

end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

theorem exists_three_chart_quasimodes_with_gaps_oai :
    ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
      ∀ g ∈ N, ∀ a b : ℝ, 0<a → a<b → b<R/2 → ∀ A : ℝ,
      ∃ Φ : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ Φ ∧
        ContDiff ℝ ∞ (Φ ∘ threeNormalInv) ∧ ∃ δ>0,
        (∀ y∈closedBall 0 a, threeGlobalLog (threeNormalInv y)+δ<Φ (threeNormalInv y)) ∧
        (∀ p ∉ threeNormalInv '' closedBall 0 b, Φ p≤threeGlobalLog p-2*δ) ∧
        ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
        ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
          (∀ J∈partition, 0<ℓ J) ∧ ∃ ε>0,
        ∀ m D : ℕ, ∃ C>0, ∀ᶠ k : ℕ in atTop,
          ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
            tsupport u ⊆ ball 0 ((b+R/2)/2) ∧
            (∀ x : NormalWaveSpace, ∀ j ≤ m,
              ‖iteratedFDeriv ℝ j u x‖ ≤ C*(productWaveFrequency k)^(j+4)*
                Real.exp (productWaveFrequency k*Φ (threeNormalInv x)) ∧
              ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (threeNormalMetricOf g) u y+
                  productFrequency k*u y) x‖ ≤ C*((productWaveFrequency k)^(D+1))⁻¹*
                Real.exp (productWaveFrequency k*Φ (threeNormalInv x))) ∧
            (∀ y∈threeExceptionalInChart Φ k,
              1/(productWaveFrequency k)^110 ≤ ‖realWaveJet (productWaveFrequency k) (threePacketWeight Φ k y)
                (((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) ∘ normalWaveEquiv) y‖) ∧
            ENNReal.ofReal (A*productWaveFrequency k) < SignTests.signCertificate
              (fun z : {J : Box (Fin 3) // J∈partition.boxes} => Box.Ioo z.val)
              (fun z => ε/(productWaveFrequency k*ℓ z.val))
              (((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) ∘ normalWaveEquiv) ∧
            ENNReal.ofReal (A*productWaveFrequency k) < 36*Measure.hausdorffMeasure 2
              ((⋃ z : {J : Box (Fin 3) // J∈partition.boxes}, Box.Ioo z.val) ∩
                {x | ((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) (normalWaveEquiv x)=0}) := by
  obtain ⟨C₀,R,hR,hclean,N,hN,h0N,hprofiles⟩ := exists_three_robust_global_profile_family
  refine ⟨R,hR,hclean,N,hN,h0N,?_⟩
  intro g hg a b ha hab hbR A
  let G := threeNormalMetricOf g
  let K : Set NormalWaveSpace := closedBall 0 b
  let O : Set NormalWaveSpace := ball 0 ((b+R/2)/2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hO : IsOpen O := isOpen_ball
  have hKO : K⊆O := closedBall_subset_ball (by linarith)
  obtain ⟨ε,hε,hε1,p₀,hp₀,hproduce⟩ :=
    exists_supported_box_nodal_quasimodes_subregions G hK hO hKO
  let c := p₀/(16*ε)
  have hc : 0 < c := div_pos hp₀ (mul_pos (by norm_num) hε)
  obtain ⟨δ,hδ,I,hIa,hprofiles⟩ := hprofiles g hg a b ha hab hbR
  obtain ⟨Φ,hΦ,hφ,hsp,hstrict,hin,hout,hmass⟩ := hprofiles (A/c)
  let φ := Φ ∘ threeNormalInv
  have hIK : normalWaveEquiv '' Box.Icc I⊆K :=
    hIa.trans (closedBall_subset_closedBall hab.le)
  obtain ⟨partition,hπ,ℓ,hℓ,hproduce⟩ := hproduce φ hφ
    (fun y hy _ => (hstrict y hy).2)
    (fun y hy hd => ((hstrict y hy).1 ((coordinateMetricGradient_eq_zero_iff G φ y).mpr hd)).elim)
    I hIK
  have hmass' : A < c*(∫ x in Box.Icc I, profileFrequencyScale G φ (normalWaveEquiv x)) :=
    (div_lt_iff₀ hc).mp hmass |>.trans_eq (mul_comm _ _)
  obtain ⟨r,hr⟩ := (hK.image normalWaveEquiv.symm.continuous).isBounded.subset_closedBall (0:Fin 3 → ℝ)
  let S : Set (Fin 3 → ℝ) := closedBall 0 r
  obtain ⟨T,hT,H,hH,hinputs⟩ := threePacket_background_input_bounds hφ (isCompact_closedBall (0:Fin 3 → ℝ) r)
  refine ⟨Φ,hΦ,hφ,δ/2,half_pos hδ,hin,(by simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hout),I,hIa,partition,hπ,ℓ,hℓ,ε,hε,?_⟩
  intro m D
  obtain ⟨c₀,hc₀,C,hC,N₀,hN₀,hproduce⟩ := hproduce m D T H hT.le hH.le
  refine ⟨C,hC,?_⟩
  have hfreq := productWaveFrequency_tendsto.eventually (eventually_ge_atTop N₀)
  have hsign := three_background_sign_small Φ (half_pos hδ)
    (K:=normalWaveEquiv '' Box.Icc I) (fun y hy => (hin y (hIa hy)).le) hc₀
  have hexcept := three_exceptional_eventually_coverage Φ hδ (K:=K) (fun y hy =>
    hout (threeNormalInv y) (by
      rintro ⟨x,hx,hxy⟩
      exact hy (threeNormalInv_injective hxy ▸ hx)))
  filter_upwards [hfreq,eventually_ge_atTop (2:ℕ),hsign,hexcept] with k hk hk2 hsign hexcept
  obtain ⟨hW,hW0,hwjet,hlog⟩ := hinputs k hk2
  have hw : ContDiff ℝ ∞ (threeCoupled threeCouplingRadius k ∘ threeNormalInv) :=
    (threeCoupled_chart_smooth _ _ _).comp threeNormalEquiv.contDiff
  obtain ⟨u,hu,huc,hus,hder,hjet,hscore,hnod⟩ := hproduce (productWaveFrequency k) hk S
    (convex_closedBall _ _) (threeExceptionalInChart Φ k) (hexcept.trans hr) hexcept
    (threeCoupled threeCouplingRadius k ∘ threeNormalInv) hw
    (threePacketWeight Φ k) hW hW0 (fun y _ => threePacketWeight_lower Φ k y)
    (fun y hy => threePacketWeight_upper Φ k y hy) hwjet hlog hsign
  have hν : 0<productWaveFrequency k := zero_lt_one.trans_le (hN₀.trans hk)
  have hle : A*productWaveFrequency k ≤ c*productWaveFrequency k*
      (∫ x in Box.Icc I, profileFrequencyScale G φ (normalWaveEquiv x)) := by
    nlinarith [mul_pos (sub_pos.mpr hmass') hν]
  refine ⟨u,hu,huc,hus,?_,hjet,(ENNReal.ofReal_le_ofReal hle).trans_lt hscore,
    (ENNReal.ofReal_le_ofReal hle).trans_lt hnod⟩
  simpa only [productWaveFrequency_equation,G,φ,Function.comp_apply] using hder
end


open Set Filter Function Manifold Metric
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_three_chart_quasimodes_with_gaps_oai := @OAI.YauCounterexamples.exists_three_chart_quasimodes_with_gaps_oai
