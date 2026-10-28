-- Prove2me | solution 1 for OAI.YauCounterexamples.threeCoupled_ambient_derivative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:26:00.495289+00:00
-- url     : https://prove2.me/submissions/5f6cf95b-76d4-4b83-9898-e57b62ffc17e

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

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

lemma unitSphereFrame_orthogonal (p : Metric.sphere (0 : A) 1) (w : Euclidean n) :
    inner ℝ (p : A) (unitSphereFrame p w) = 0 := by
  have hh := ((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm w).property
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hh
  change inner ℝ (p : A) _ = 0
  rw [real_inner_comm]
  change inner ℝ _ (-(p : A)) = 0 at hh
  rw [inner_neg_right,neg_eq_zero] at hh
  exact hh

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
local instance threeFirstContinuousSMul_re3fd5f_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
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
local instance threeCoupledContinuousSMul_re3fd5f_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
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
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFormulaNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples

attribute [local instance] OAI.YauCounterexamples.threeFormula_dimension_fact
lemma threeCoupled_ambient_derivative_oai (r : ℝ) (k : ℕ) (hk : 1 ≤ k) (p : ThreeManifold)
    (v : ThreeModel) :
    fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0 v=
      inner ℝ (unitSphereFrame (n:=2) p.1 v.fst) (threeAmbientSphereGradient r k p)+
      inner ℝ (unitSphereFrame (n:=1) p.2 v.snd) (threeAmbientCircleGradient r k p) := by
  rw [threeCoupled_chart_first]
  have hz : (p.2:ℂ)^(k-1)*(p.2:ℂ)=(p.2:ℂ)^k := by rw [←pow_succ,Nat.sub_add_cancel hk]
  have horth := unitSphereFrame_orthogonal (n:=1) p.2 v.snd
  have hn : Complex.normSq (p.2:ℂ)=1 := by rw [Complex.normSq_eq_norm_sq,p.2.norm_coe]; norm_num
  have hrot : unitSphereFrame (n:=1) p.2 v.snd=
      inner ℝ (unitSphereFrame (n:=1) p.2 v.snd) (Complex.I*(p.2:ℂ)) • (Complex.I*(p.2:ℂ)) := by
    apply Complex.ext <;> simp only [Complex.inner,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      zero_mul,one_mul,sub_zero,zero_add,Complex.real_smul,Complex.ofReal_re,Complex.ofReal_im,
      Complex.conj_re,Complex.conj_im,Complex.normSq_apply] at *
    · linear_combination -((unitSphereFrame (n:=1) p.2 v.snd).re)*hn + ((p.2:ℂ).re)*horth
    · linear_combination -((unitSphereFrame (n:=1) p.2 v.snd).im)*hn + ((p.2:ℂ).im)*horth
  let α := (p.2:ℂ)^k*productA p.1^(k-1)
  let β := (p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)
  have hs : (k:ℂ)*(p.2:ℂ)^k*(productA p.1^(k-1)*productA (unitSphereFrame (n:=2) p.1 v.fst)+
        (r:ℂ)^k*productB p.1^(k-1)*productB (unitSphereFrame (n:=2) p.1 v.fst))=
      (k:ℂ)*(α*productA (unitSphereFrame (n:=2) p.1 v.fst)+β*productB (unitSphereFrame (n:=2) p.1 v.fst)) := by
    dsimp [α,β]; ring
  have hep : (k:ℂ)*(p.2:ℂ)^(k-1)*(unitSphereFrame (n:=1) p.2 v.snd)*
      (productA p.1^k+(r:ℂ)^k*productB p.1^k)=
      ((inner ℝ (unitSphereFrame (n:=1) p.2 v.snd) (Complex.I*(p.2:ℂ))):ℂ)*
        (k:ℂ)*Complex.I*threeCoupledComplex r k p := by
    conv_lhs => rw [hrot]
    dsimp only [threeCoupledComplex]
    simp only [Complex.real_smul]
    rw [←hz]
    ring
  rw [hs,hep]
  change _ = inner ℝ (unitSphereFrame (n:=2) p.1 v.fst)
    ((k:ℝ) • ((α.re+β.re) • productAxis 0-α.im • productAxis 1-β.im • productAxis 2))+
    inner ℝ (unitSphereFrame (n:=1) p.2 v.snd)
      ((-(k:ℝ)*(threeCoupledComplex r k p).im) • (Complex.I*(p.2:ℂ)))
  simp only [inner_smul_right,inner_sub_right]
  have haxis (i : Fin 3) : inner ℝ (unitSphereFrame (n:=2) p.1 v.fst) (productAxis i)=
      (unitSphereFrame (n:=2) p.1 v.fst) i := by rw [real_inner_comm,productAxis_coord]
  simp only [haxis,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,productA_re,productA_im,
    productB_re,productB_im]
  ring
end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.threeCoupled_ambient_derivative_oai := @OAI.YauCounterexamples.threeCoupled_ambient_derivative_oai
