-- Prove2me | solution 1 for OAI.YauCounterexamples.threeCoupled_profile_rank_somewhere
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:30:51.261207+00:00
-- url     : https://prove2.me/submissions/852bf820-051f-4824-a209-70cb2846f4dc

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_exists_threeInteriorMeridianEnergy_deriv

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_DirectionalLinearComp
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma directional_linear_comp (L : E →L[ℝ] F) {f : F → ℂ}
    (hf : Differentiable ℝ f) (x v : E) :
    fderiv ℝ (f ∘ L) x v = fderiv ℝ f (L x) (L v) := by
  rw [fderiv_comp x (hf _) L.differentiableAt,L.fderiv]
  rfl
lemma directional_mul_complex {f g : E → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x v : E) :
    fderiv ℝ (fun y => f y*g y) x v = fderiv ℝ f x v*g x+f x*fderiv ℝ g x v := by
  have hh := ((hf x).hasFDerivAt.mul (hg x).hasFDerivAt).fderiv
  change fderiv ℝ (f*g) x v = _
  rw [hh]
  simp [smul_eq_mul,mul_comm,add_comm]
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
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]

lemma unitSphereFrame_coordinates (p : Metric.sphere (0 : A) 1) (a : A) :
    unitSphereFrame (n:=n) p (unitSphereCoordinates (n:=n) p a) = unitSphereProjection p a := by
  change (((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm
      ((OrthonormalBasis.fromOrthogonalSpanSingleton n
        (ne_zero_of_mem_unit_sphere (-p))).repr ⟨unitSphereProjection p a,_⟩)) : A) = _
  rw [LinearIsometryEquiv.symm_apply_apply]


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
omit [FiniteDimensional ℝ A] in
lemma productSphere_fstPower_zero (p : Metric.sphere (0:A) 1) (ℓ : A →L[ℝ] ℂ) (k : ℕ) :
    productSphere_fstPower (n:=n) (m:=m) p ℓ k 0 = (ℓ p)^k := by
  simp [productSphere_fstPower,roundChart_zero]
omit [FiniteDimensional ℝ A] in
lemma productSphere_fstPower_first (p : Metric.sphere (0:A) 1) (ℓ : A →L[ℝ] ℂ) (k : ℕ)
    (v : WithLp 2 (Euclidean n×Euclidean m)) :
    fderiv ℝ (productSphere_fstPower p ℓ k) 0 v =
      (k:ℂ)*(ℓ p)^(k-1)*ℓ (unitSphereFrame (n:=n) p v.fst) := by
  unfold productSphere_fstPower
  have hf : ContDiff ℝ ∞ (fun y : Euclidean n => (ℓ (roundChart (p:A) (unitSphereFrame (n:=n) p) y))^k) := (ℓ.contDiff.comp (roundChart_smooth _ _)).pow k
  rw [directional_linear_comp (WithLp.fstL 2 ℝ (Euclidean n) (Euclidean m)) (f:=(fun y : Euclidean n => (ℓ (roundChart (p:A) (unitSphereFrame (n:=n) p) y))^k)) (hf.differentiable (by simp))]
  simp only [ContinuousLinearMap.map_zero]
  rw [roundLinearPower_directional]
  simp [roundChart_zero,(roundChart_first _ _).fderiv]
omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_smooth (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ) (k : ℕ) :
    ContDiff ℝ ∞ (productSphere_sndPower (n:=n) (m:=m) p ℓ k) :=
  ((ℓ.contDiff.comp (roundChart_smooth _ _)).pow k).comp
    (WithLp.sndL 2 ℝ (Euclidean n) (Euclidean m)).contDiff
omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_zero (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ) (k : ℕ) :
    productSphere_sndPower (n:=n) (m:=m) p ℓ k 0 = (ℓ p)^k := by
  simp [productSphere_sndPower,roundChart_zero]
omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_first (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ) (k : ℕ)
    (v : WithLp 2 (Euclidean n×Euclidean m)) :
    fderiv ℝ (productSphere_sndPower p ℓ k) 0 v =
      (k:ℂ)*(ℓ p)^(k-1)*ℓ (unitSphereFrame (n:=m) p v.snd) := by
  unfold productSphere_sndPower
  have hf : ContDiff ℝ ∞ (fun y : Euclidean m => (ℓ (roundChart (p:B) (unitSphereFrame (n:=m) p) y))^k) := (ℓ.contDiff.comp (roundChart_smooth _ _)).pow k
  rw [directional_linear_comp (WithLp.sndL 2 ℝ (Euclidean n) (Euclidean m)) (f:=(fun y : Euclidean m => (ℓ (roundChart (p:B) (unitSphereFrame (n:=m) p) y))^k)) (hf.differentiable (by simp))]
  simp only [ContinuousLinearMap.map_zero]
  rw [roundLinearPower_directional]
  simp [roundChart_zero,(roundChart_first _ _).fderiv]
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


end

open Set Filter Manifold
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

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
open Set Filter Manifold
open scoped Topology ContDiff Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contMDiff_coordinateGradientPair {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (coordinateGradientPair g u v) := by
  have he : coordinateGradientPair g u v = fun x => (2 : ℝ)⁻¹ *
      (laplaceBeltrami g (fun y => u y * v y) x -
        u x * laplaceBeltrami g v x - v x * laplaceBeltrami g u x) := by
    funext x
    rw [laplaceBeltrami_mul (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hv.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    ring
  rw [he]
  exact contMDiff_const.mul (((contMDiff_laplaceBeltrami (hu.mul hv) g).sub
    (hu.mul (contMDiff_laplaceBeltrami hv g))).sub (hv.mul (contMDiff_laplaceBeltrami hu g)))

end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal



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
lemma three_chart_center (p : ThreeManifold) : chartAt ThreeModel p p = 0 := by
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · exact sphere_chart_center p.1
  · exact unitSphere_chart_center (n:=1) p.2
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
local instance threeModelContinuousSMul'_r50a734_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.threeAmbientNormedSpace'
local instance threeAmbientContinuousSMul'_r50a734_1 : ContinuousSMul ℝ ThreeAmbient := inferInstance
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
local instance threeFirstContinuousSMul_r50a734_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.sphereFirst_dimension_fact
lemma threeComplexPower_chart_smooth (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) :
    ContDiff ℝ ∞ (threeComplexPower a b k ∘ (chartAt ThreeModel p).symm) := by
  rw [threeComplexPower_chart]
  exact (productSphere_fstPower_smooth _ _ _).mul (productSphere_sndPower_smooth _ _ _)
lemma threeComplexPower_chart_first (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) (v : ThreeModel) :
    fderiv ℝ (threeComplexPower a b k ∘ (chartAt ThreeModel p).symm) 0 v =
      (k:ℂ)*(planarLinear a b (p.1:Euclidean 3))^(k-1)*
        planarLinear a b (unitSphereFrame (n:=2) p.1 v.fst)*(p.2:ℂ)^k+
      (planarLinear a b (p.1:Euclidean 3))^k*(k:ℂ)*(p.2:ℂ)^(k-1)*
        unitSphereFrame (n:=1) p.2 v.snd := by
  rw [threeComplexPower_chart]
  erw [directional_mul_complex
    ((productSphere_fstPower_smooth _ _ _).differentiable (by simp))
    ((productSphere_sndPower_smooth _ _ _).differentiable (by simp))]
  erw [productSphere_fstPower_first,productSphere_sndPower_first,
    productSphere_fstPower_zero,productSphere_sndPower_zero]
  simp only [complexIdentityPlanar]
  ring
lemma threePower_chart_first (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) (v : ThreeModel) :
    fderiv ℝ (threePower a b k ∘ (chartAt ThreeModel p).symm) 0 v =
      ((k:ℂ)*(planarLinear a b (p.1:Euclidean 3))^(k-1)*
        planarLinear a b (unitSphereFrame (n:=2) p.1 v.fst)*(p.2:ℂ)^k+
      (planarLinear a b (p.1:Euclidean 3))^k*(k:ℂ)*(p.2:ℂ)^(k-1)*
        unitSphereFrame (n:=1) p.2 v.snd).re := by
  change fderiv ℝ (fun x => (threeComplexPower a b k ((chartAt ThreeModel p).symm x)).re) 0 v = _
  exact (fderiv_real_part ((threeComplexPower_chart_smooth a b k p).differentiable (by simp) 0) v).trans
    (congrArg Complex.re (threeComplexPower_chart_first a b k p v))
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
local instance threeCoupledContinuousSMul_r50a734_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeCoupled_smooth (r : ℝ) (k : ℕ) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeCoupled r k) := by
  rw [threeCoupled_eq]
  exact (threePower_smooth _ _ _).add (contMDiff_const.mul (threePower_smooth _ _ _))

attribute [local instance] OAI.YauCounterexamples.threeCoupled_dimension_fact
lemma threeCoupled_chart_first (r : ℝ) (k : ℕ) (p : ThreeManifold) (v : ThreeModel) :
    fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0 v =
      ((k:ℂ)*(p.2:ℂ)^k*(productA p.1^(k-1)*productA (unitSphereFrame (n:=2) p.1 v.fst)+
        (r:ℂ)^k*productB p.1^(k-1)*productB (unitSphereFrame (n:=2) p.1 v.fst))+
      (k:ℂ)*(p.2:ℂ)^(k-1)*unitSphereFrame (n:=1) p.2 v.snd*
        (productA p.1^k+(r:ℂ)^k*productB p.1^k)).re := by
  rw [threeCoupled_eq]
  change fderiv ℝ (fun y => (threePower (productAxis 0) (productAxis 1) k ∘ (chartAt ThreeModel p).symm) y +
    r^k*(threePower (productAxis 0) (productAxis 2) k ∘ (chartAt ThreeModel p).symm) y) 0 v = _
  have ha := (Complex.reCLM.contDiff.comp (threeComplexPower_chart_smooth (productAxis 0) (productAxis 1) k p)).differentiable (by simp)
  have hb := (Complex.reCLM.contDiff.comp (threeComplexPower_chart_smooth (productAxis 0) (productAxis 2) k p)).differentiable (by simp)
  erw [fderiv_fun_add (ha 0) ((differentiableAt_const _).mul (hb 0)),fderiv_const_mul (hb 0)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  erw [threePower_chart_first,threePower_chart_first]
  rw [←Complex.re_ofReal_mul,←Complex.add_re]
  apply congrArg Complex.re
  change _ = (k:ℂ)*(p.2:ℂ)^k*(planarLinear _ _ _^(k-1)*planarLinear _ _ _+
        (r:ℂ)^k*planarLinear _ _ _^(k-1)*planarLinear _ _ _)+
      (k:ℂ)*(p.2:ℂ)^(k-1)*unitSphereFrame (n:=1) p.2 v.snd*
        (planarLinear _ _ _^k+(r:ℂ)^k*planarLinear _ _ _^k)
  push_cast
  ring
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ThreeDirectionsNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
lemma productCircle_projection (p : Circle) :
    unitSphereProjection p (Complex.I*(p:ℂ))=Complex.I*(p:ℂ) := by
  have hi : inner ℝ (p:ℂ) (Complex.I*(p:ℂ))=0 := by
    simp [Complex.inner,Complex.mul_re,Complex.mul_im]; ring
  simp [unitSphereProjection,hi]
attribute [local instance] OAI.YauCounterexamples.threeDirections_dimension_fact
lemma threeCoupled_circle_direction (r : ℝ) (k : ℕ) (hk : 1≤k) (p : ThreeManifold) :
    fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0 (threeCircleDirection p)=
      -(k:ℝ)*(threeCoupledComplex r k p).im := by
  rw [threeCoupled_chart_first]
  change ((k:ℂ)*(p.2:ℂ)^k*(productA p.1^(k-1)*productA (unitSphereFrame (n:=2) p.1 0)+
    (r:ℂ)^k*productB p.1^(k-1)*productB (unitSphereFrame (n:=2) p.1 0))+
    (k:ℂ)*(p.2:ℂ)^(k-1)*unitSphereFrame (n:=1) p.2 (unitSphereCoordinates (n:=1) p.2 (Complex.I*(p.2:ℂ)))*(productA p.1^k+(r:ℂ)^k*productB p.1^k)).re = _
  simp only [map_zero,productA,productB,mul_zero,add_zero,zero_add]
  erw [unitSphereFrame_coordinates,productCircle_projection]
  have hp : (p.2:ℂ)^(k-1)*(p.2:ℂ)=(p.2:ℂ)^k := by rw [←pow_succ,Nat.sub_add_cancel hk]
  have he : (k:ℂ)*(p.2:ℂ)^(k-1)*(Complex.I*(p.2:ℂ))*(productA p.1^k+(r:ℂ)^k*productB p.1^k)=
      (k:ℂ)*Complex.I*threeCoupledComplex r k p := by
    dsimp only [threeCoupledComplex]
    rw [←hp]
    ring
  change ((k:ℂ)*(p.2:ℂ)^(k-1)*(Complex.I*(p.2:ℂ))*(productA p.1^k+(r:ℂ)^k*productB p.1^k)).re = _
  rw [he]
  simp [Complex.mul_re,Complex.mul_im]
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeRankNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
section Curve
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
lemma inChart_deriv_curve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ γ)
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (c : ℝ) :
    fderiv ℝ (u ∘ (chartAt E (γ c)).symm) ((chartAt E (γ c)) (γ c))
      (deriv ((chartAt E (γ c)) ∘ γ) c)=deriv (u ∘ γ) c := by
  let e := chartAt E (γ c)
  have he : γ c ∈ e.source := mem_chart_source E (γ c)
  have hc : ContDiffAt ℝ ∞ (e ∘ γ) c :=
    ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (γ c)) he).comp c hγ.contMDiffAt).contDiffAt
  have hf := (contDiffAt_inChart hu (γ c) (e.map_source he)).differentiableAt (by simp)
  have hder := hf.hasFDerivAt.comp_hasDerivAt c (hc.differentiableAt (by simp)).hasDerivAt
  have hEq : (u ∘ e.symm) ∘ (e ∘ γ) =ᶠ[𝓝 c] u ∘ γ := by
    filter_upwards [hγ.continuous.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds he)] with t ht
    simp only [Function.comp_apply,e.left_inv ht]
  simpa only [e] using (hder.congr_of_eventuallyEq hEq.symm).deriv.symm
lemma linear_prod_surjective_of_directions (L R : E →L[ℝ] ℝ) (v w : E)
    (hLv : L v ≠ 0) (hLw : L w=0) (hRw : R w≠0) : Function.Surjective (L.prod R) := by
  rintro ⟨a,b⟩
  refine ⟨(a/L v) • v+((b-(a/L v)*R v)/R w) • w,?_⟩
  apply Prod.ext
  · change L ((a/L v) • v+((b-(a/L v)*R v)/R w) • w)=a
    simp only [map_add,map_smul,smul_eq_mul,hLw,mul_zero,add_zero]
    exact div_mul_cancel₀ a hLv
  · change R ((a/L v) • v+((b-(a/L v)*R v)/R w) • w)=b
    simp only [map_add,map_smul,smul_eq_mul]
    rw [div_mul_cancel₀ _ hRw]
    ring
end Curve

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_ProductMetric_ThreeInteriorMeridianNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeInteriorMeridian_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩

attribute [local instance] OAI.YauCounterexamples.threeInteriorMeridianNormedSpace
local instance threeInteriorMeridianContinuousSMul_r50a734_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma threeInteriorMeridian_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ThreeModel) ∞ threeInteriorMeridian := by
  have h : ContDiff ℝ ∞ threeInteriorMeridianAmbient :=
    (Real.contDiff_cos.smul contDiff_const).add (Real.contDiff_sin.smul contDiff_const)
  have hs := h.contMDiff.codRestrict_sphere (n:=2) (fun t => (threeInteriorMeridian t).1.property)
  apply contMDiff_reModel_target threeModelEquiv
  rw [modelWithCornersSelf_prod]
  exact hs.prodMk contMDiff_const
lemma threeInteriorMeridian_A (t : ℝ) : productA (threeInteriorMeridian t).1=((Real.cos t:ℝ):ℂ)*Complex.I := by
  apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,mul_one] <;> simp [productA_re,productA_im,threeInteriorMeridian,threeInteriorMeridianAmbient,productAxis]
lemma threeInteriorMeridian_B (t : ℝ) : productB (threeInteriorMeridian t).1=((Real.sin t:ℝ):ℂ)*Complex.I := by
  apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,mul_one] <;> simp [productB_re,productB_im,threeInteriorMeridian,threeInteriorMeridianAmbient,productAxis]
lemma threeInteriorMeridian_circle (t : ℝ) : ((threeInteriorMeridian t).2:ℂ)=1 := by rfl
lemma interior_complex_I_pow_four_add_one (m : ℕ) : Complex.I^(4*m+1)=Complex.I := by
  rw [pow_add,pow_mul]
  norm_num
lemma threeInteriorMeridian_complex (r t : ℝ) (m : ℕ) :
    threeCoupledComplex r (4*m+1) (threeInteriorMeridian t)=
      (((Real.cos t)^(4*m+1)+r^(4*m+1)*(Real.sin t)^(4*m+1):ℝ):ℂ)*Complex.I := by
  simp only [threeCoupledComplex,threeInteriorMeridian_A,threeInteriorMeridian_B,threeInteriorMeridian_circle,mul_pow,
    interior_complex_I_pow_four_add_one,one_pow]
  simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow]
  ring
lemma threeInteriorMeridian_zero (r t : ℝ) (m : ℕ) : threeCoupled r (4*m+1) (threeInteriorMeridian t)=0 := by
  rw [threeCoupled,threeInteriorMeridian_complex]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero]
lemma threeInteriorMeridian_circle_deriv_ne (r : ℝ) (hr : 0 < r) (m : ℕ) {c : ℝ}
    (hc : c ∈ Ioo 0 (Real.pi/2)) :
    fderiv ℝ (threeCoupled r (4*m+1) ∘ (chartAt ThreeModel (threeInteriorMeridian c)).symm) 0
      (threeCircleDirection (threeInteriorMeridian c)) ≠ 0 := by
  rw [threeCoupled_circle_direction r (4*m+1) (by omega),threeInteriorMeridian_complex]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero]
  have hcos : 0<Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hc.1],hc.2⟩
  have hsin : 0<Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have hk : (0:ℝ)<(4*m+1:ℕ) := by positivity
  exact mul_ne_zero (neg_ne_zero.mpr hk.ne') (by positivity)
lemma exists_threeCoupled_interior_gradient_rank (r : ℝ) (hr : 0 < r) (hr1 : r<1) {m : ℕ} (hm : 1 ≤ m) :
    ∃ c ∈ Ioo 0 (Real.pi/2), Function.Surjective (fderiv ℝ
      (fun y => (threeCoupled r (4*m+1) ((chartAt ThreeModel (threeInteriorMeridian c)).symm y),
        coordinateGradientPair threeBackgroundMetric (threeCoupled r (4*m+1))
          (threeCoupled r (4*m+1)) ((chartAt ThreeModel (threeInteriorMeridian c)).symm y))) 0) := by
  obtain ⟨c,hc,hR⟩ := exists_threeInteriorMeridianEnergy_deriv r hr hr1 hm
  refine ⟨c,hc,?_⟩
  let e := chartAt ThreeModel (threeInteriorMeridian c)
  let u := threeCoupled r (4*m+1)
  let R := coordinateGradientPair threeBackgroundMetric u u
  have hu := threeCoupled_smooth r (4*m+1)
  have hRs := contMDiff_coordinateGradientPair hu hu threeBackgroundMetric
  have ht : (0:ThreeModel) ∈ e.target := by rw [three_chart_target]; trivial
  have hud := (contDiffAt_inChart hu (threeInteriorMeridian c) ht).differentiableAt (by simp)
  have hRd := (contDiffAt_inChart hRs (threeInteriorMeridian c) ht).differentiableAt (by simp)
  change Function.Surjective (fderiv ℝ (fun y => ((u ∘ e.symm) y,(R ∘ e.symm) y)) 0)
  rw [hud.fderiv_prodMk hRd]
  apply linear_prod_surjective_of_directions _ _ (threeCircleDirection (threeInteriorMeridian c))
    (deriv (e ∘ threeInteriorMeridian) c)
  · exact threeInteriorMeridian_circle_deriv_ne r hr m hc
  · have hh := inChart_deriv_curve threeInteriorMeridian_smooth hu c
    rw [three_chart_center] at hh
    have hz : u ∘ threeInteriorMeridian = fun _ => 0 := funext (fun t => threeInteriorMeridian_zero r t m)
    change fderiv ℝ (u ∘ e.symm) 0 (deriv (e ∘ threeInteriorMeridian) c)=deriv (u ∘ threeInteriorMeridian) c at hh
    simpa only [hz,deriv_const] using hh
  · have hh := inChart_deriv_curve threeInteriorMeridian_smooth hRs c
    rw [three_chart_center] at hh
    exact hh.trans_ne hR

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeAnalyticNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeAnalytic_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
lemma threeInteriorMeridian_mem_profile_source (t : ℝ) :
    threeInteriorMeridian t ∈ (chartAt ThreeModel threeProfileCenter).source := by
  change threeInteriorMeridian t ∈ ((chartAt ThreeProductModel threeProfileCenter).trans
    threeModelEquiv.toHomeomorph.toOpenPartialHomeomorph).source
  simp only [OpenPartialHomeomorph.trans_source,Homeomorph.toOpenPartialHomeomorph_source,
    preimage_univ,inter_univ]
  change threeInteriorMeridian t ∈ (chartAt (Euclidean 2) threeProfileCenter.1).source ×ˢ
    (chartAt (Euclidean 1) threeProfileCenter.2).source
  constructor
  · change (threeInteriorMeridian t).1 ∈ (stereographic' 2 (-threeProfileCenter.1)).source
    rw [stereographic'_source]
    intro h
    have hh := congrArg (fun p : Sphere 2 => (p:Euclidean 3) 0) h
    norm_num [threeInteriorMeridian,threeInteriorMeridianAmbient,threeProfileCenter,
      threeProfilePoint,productAxis,PiLp.single_apply,Fin.ext_iff] at hh
  · change (1:Circle) ∈ (stereographic' 1 (-(1:Circle))).source
    erw [stereographic'_source]
    intro h
    have hh := congrArg (fun z : Circle => (z:ℂ).re) h
    norm_num at hh
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ChartPairRankTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
lemma chart_pair_rank_transfer {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M]
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (p q : M) (hq : q ∈ (chartAt E p).source)
    (hr : Function.Surjective (fderiv ℝ (fun y => (u ((chartAt E q).symm y),v ((chartAt E q).symm y)))
      (chartAt E q q))) :
    Function.Surjective (fderiv ℝ (fun y => (u ((chartAt E p).symm y),v ((chartAt E p).symm y)))
      (chartAt E p q)) := by
  let e := chartAt E p
  let f := chartAt E q
  let T := e ∘ f.symm
  let H := fun y => (u (e.symm y),v (e.symm y))
  have hft : f q ∈ f.target := f.map_source (mem_chart_source E q)
  have hfs : f.symm (f q)=q := f.left_inv (mem_chart_source E q)
  have ht : DifferentiableAt ℝ T (f q) := by
    have h₁ := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℝ,E)) (n:=∞) p) hq
    have h₂ := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℝ,E)) (n:=∞) q) hft
    have h₁' : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e (f.symm (f q)) := hfs.symm ▸ h₁
    exact ((h₁'.comp (f q) h₂).contDiffAt).differentiableAt (by simp)
  have hH : DifferentiableAt ℝ H (T (f q)) := by
    have he := e.map_source hq
    have hh := (contDiffAt_inChart hu p he).prodMk (contDiffAt_inChart hv p he)
    simpa only [H,T,Function.comp_apply,hfs] using hh.differentiableAt (by simp)
  have hgerm : H ∘ T =ᶠ[𝓝 (f q)] (fun y => (u (f.symm y),v (f.symm y))) := by
    have hn : ∀ᶠ y in 𝓝 (f q), f.symm y ∈ e.source :=
      (f.continuousAt_symm hft).preimage_mem_nhds (hfs.symm ▸ e.open_source.mem_nhds hq)
    filter_upwards [hn] with y hy
    simp only [H,T,Function.comp_apply,e.left_inv hy]
  have hd := fderiv_comp (f q) hH ht
  rw [hgerm.fderiv_eq] at hd
  rw [hd] at hr
  have hh : Function.Surjective (fderiv ℝ H (T (f q))) := Function.Surjective.of_comp
    (f:=fun z => fderiv ℝ H (T (f q)) z) (g:=fun z => fderiv ℝ T (f q) z) hr
  simpa only [H,T,Function.comp_apply,hfs] using hh
lemma threeCoupled_profile_rank_somewhere_oai {m : ℕ} (hm : 1 ≤ m) :
    ∃ x : ThreeModel, Function.Surjective (fderiv ℝ
      (fun y => (threeCoupled threeCouplingRadius (4*m+1) ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair threeBackgroundMetric (threeCoupled threeCouplingRadius (4*m+1))
          (threeCoupled threeCouplingRadius (4*m+1)) ((chartAt ThreeModel threeProfileCenter).symm y))) x) := by
  obtain ⟨c,hc,hr⟩ := exists_threeCoupled_interior_gradient_rank threeCouplingRadius
    (by norm_num [threeCouplingRadius]) (by norm_num [threeCouplingRadius]) hm
  refine ⟨chartAt ThreeModel threeProfileCenter (threeInteriorMeridian c),?_⟩
  apply chart_pair_rank_transfer (threeCoupled_smooth _ _)
    (contMDiff_coordinateGradientPair (threeCoupled_smooth _ _) (threeCoupled_smooth _ _) _)
    threeProfileCenter (threeInteriorMeridian c) (threeInteriorMeridian_mem_profile_source c)
  simpa only [three_chart_center] using hr
end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.threeCoupled_profile_rank_somewhere_oai := @OAI.YauCounterexamples.threeCoupled_profile_rank_somewhere_oai
