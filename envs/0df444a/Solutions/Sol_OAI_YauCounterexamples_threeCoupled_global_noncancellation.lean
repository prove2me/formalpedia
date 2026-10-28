-- Prove2me | solution 1 for OAI.YauCounterexamples.threeCoupled_global_noncancellation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:28:15.714008+00:00
-- url     : https://prove2.me/submissions/3aedcb00-ab15-400f-88ec-9cc8c2df4437

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

lemma unitSphereCoordinates_inner (p : Metric.sphere (0 : A) 1) (a b : A) :
    inner ℝ (unitSphereCoordinates (n:=n) p a) (unitSphereCoordinates (n:=n) p b) =
      inner ℝ a b - inner ℝ (p : A) a * inner ℝ (p : A) b := by
  rw [← (unitSphereFrame (n:=n) p).inner_map_map,unitSphereFrame_coordinates,unitSphereFrame_coordinates]
  simp [unitSphereProjection,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    real_inner_comm a (p : A)]


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
local instance threeFirstContinuousSMul_r38d1c7_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
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
lemma productAxis_norm (i : Fin 3) : ‖productAxis i‖=1 := by simp [productAxis]
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
local instance threeCoupledContinuousSMul_r38d1c7_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
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
lemma productAxis_coord_le (p : Sphere 2) (i : Fin 3) : |(p:Euclidean 3) i| ≤ 1 := by
  have hn : ‖(p:Euclidean 3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.property
  have h := abs_real_inner_le_norm (productAxis i) (p:Euclidean 3)
  simpa only [productAxis_coord,productAxis_norm,hn,one_mul] using h
lemma sphereCoordinates_norm_le {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A=n+1)]
    (p : Metric.sphere (0:A) 1) (a : A) : ‖unitSphereCoordinates (n:=n) p a‖ ≤ ‖a‖ := by
  have h := unitSphereCoordinates_inner (n:=n) p a a
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at h
  nlinarith [sq_nonneg (inner ℝ (p:A) a),norm_nonneg (unitSphereCoordinates (n:=n) p a),norm_nonneg a]
lemma productA_projection (p : Sphere 2) (a : Euclidean 3) :
    productA (unitSphereProjection p a)=productA a-(inner ℝ (p:Euclidean 3) a:ℝ)*productA p := by
  simp [productA,unitSphereProjection,map_sub,map_smul,Complex.real_smul]
lemma productB_projection (p : Sphere 2) (a : Euclidean 3) :
    productB (unitSphereProjection p a)=productB a-(inner ℝ (p:Euclidean 3) a:ℝ)*productB p := by
  simp [productB,unitSphereProjection,map_sub,map_smul,Complex.real_smul]
lemma productA_axis (i : Fin 3) : productA (productAxis i) =
    (if i=0 then 1 else 0)+(if i=1 then Complex.I else 0) := by
  fin_cases i <;> apply Complex.ext <;> norm_num [productA_re,productA_im,productAxis,PiLp.single_apply,Fin.ext_iff]
lemma productB_axis (i : Fin 3) : productB (productAxis i) =
    (if i=0 then 1 else 0)+(if i=2 then Complex.I else 0) := by
  fin_cases i <;> apply Complex.ext <;> norm_num [productB_re,productB_im,productAxis,PiLp.single_apply,Fin.ext_iff]
attribute [local instance] OAI.YauCounterexamples.threeDirections_dimension_fact
lemma threeSphereDirection_norm (p : ThreeManifold) (i : Fin 3) : ‖threeSphereDirection p i‖ ≤ 1 := by
  change ‖WithLp.toLp 2 (unitSphereCoordinates (n:=2) p.1 (productAxis i),(0:Euclidean 1))‖≤1
  rw [WithLp.norm_toLp_fst]
  exact (sphereCoordinates_norm_le p.1 (productAxis i)).trans_eq (productAxis_norm i)
lemma threeCircleDirection_norm (p : ThreeManifold) : ‖threeCircleDirection p‖ ≤ 1 := by
  have hn : ‖(p.2:ℂ)‖=1 := p.2.norm_coe
  change ‖WithLp.toLp 2 ((0:Euclidean 2),unitSphereCoordinates (n:=1) p.2 (Complex.I*(p.2:ℂ)))‖≤1
  rw [WithLp.norm_toLp_snd]
  exact (sphereCoordinates_norm_le p.2 _).trans_eq (by simp [hn])
lemma productCircle_projection (p : Circle) :
    unitSphereProjection p (Complex.I*(p:ℂ))=Complex.I*(p:ℂ) := by
  have hi : inner ℝ (p:ℂ) (Complex.I*(p:ℂ))=0 := by
    simp [Complex.inner,Complex.mul_re,Complex.mul_im]; ring
  simp [unitSphereProjection,hi]
lemma threeCoupled_sphere_direction (r : ℝ) (k : ℕ) (hk : 1≤k) (p : ThreeManifold) (i : Fin 3) :
    fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0 (threeSphereDirection p i)=
      (k:ℝ)*(((p.2:ℂ)^k*productA p.1^(k-1)*productA (productAxis i)+
        (p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)*productB (productAxis i)).re-
        (p.1:Euclidean 3) i*threeCoupled r k p) := by
  rw [threeCoupled_chart_first]
  change ((k:ℂ)*(p.2:ℂ)^k*(productA p.1^(k-1)*productA (unitSphereFrame (n:=2) p.1 (unitSphereCoordinates (n:=2) p.1 (productAxis i)))+
    (r:ℂ)^k*productB p.1^(k-1)*productB (unitSphereFrame (n:=2) p.1 (unitSphereCoordinates (n:=2) p.1 (productAxis i))))+
    (k:ℂ)*(p.2:ℂ)^(k-1)*unitSphereFrame (n:=1) p.2 0*(productA p.1^k+(r:ℂ)^k*productB p.1^k)).re = _
  rw [map_zero,mul_zero,zero_mul,add_zero,unitSphereFrame_coordinates,productA_projection,productB_projection,real_inner_comm,productAxis_coord]
  have hp (z : ℂ) : z^(k-1)*z=z^k := by rw [←pow_succ,Nat.sub_add_cancel hk]
  have he : (k:ℂ)*(p.2:ℂ)^k*(productA p.1^(k-1)*(productA (productAxis i)-((p.1:Euclidean 3) i:ℂ)*productA p.1)+
    (r:ℂ)^k*productB p.1^(k-1)*(productB (productAxis i)-((p.1:Euclidean 3) i:ℂ)*productB p.1))=
    (k:ℂ)*((p.2:ℂ)^k*productA p.1^(k-1)*productA (productAxis i)+(p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)*productB (productAxis i)-
      ((p.1:Euclidean 3) i:ℂ)*threeCoupledComplex r k p) := by
    dsimp only [threeCoupledComplex]
    rw [←hp (productA p.1),←hp (productB p.1)]
    ring
  rw [he]
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,
    Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,threeCoupled]
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ThreeNoncancelNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff
lemma complex_coefficient_norm_le (C D : ℂ) :
    ‖C‖ ≤ |(C+D).re|+|C.im|+‖D‖ := by
  have hh : |C.re| ≤ |(C+D).re|+|D.re| := by
    have h := abs_sub_le (C+D).re 0 D.re
    simpa only [Complex.add_re,add_sub_cancel_right,sub_zero,zero_sub,abs_neg] using h
  have hd := Complex.abs_re_le_norm D
  have hc := Complex.norm_le_abs_re_add_abs_im C
  linarith
lemma coupled_power_comparison {x y r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) {k : ℕ} (hk : 2 ≤ k)
    (h : x^(k-1) ≤ 2*r^k*y^(k-1)) : x^k ≤ 4*r*r^k*y^k := by
  have hpow (z : ℝ) : z^(k-1)*z=z^k := by rw [← pow_succ,Nat.sub_add_cancel (by omega)]
  have htwo : (2:ℝ) ≤ 2^(k-1) := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : 1 ≤ k-1))
  have hcoef : 2*r^k ≤ (2*r)^(k-1) := by
    rw [mul_pow]
    calc
      _ = (2*r)*r^(k-1) := by rw [← hpow r]; ring
      _ ≤ 2^(k-1)*r^(k-1) := mul_le_mul_of_nonneg_right (by nlinarith) (pow_nonneg hr _)
  have hxy : x ≤ 2*r*y := by
    apply le_of_pow_le_pow_left₀ (by omega : k-1≠0) (by positivity)
    rw [mul_pow]
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hy _))
  calc
    _ = x*x^(k-1) := by rw [mul_comm,hpow]
    _ ≤ (2*r*y)*(2*r^k*y^(k-1)) := mul_le_mul hxy h (pow_nonneg hx _) (by positivity)
    _ = 4*r*r^k*y^k := by rw [← hpow y]; ring

lemma coupled_power_uniform_bound {A B w : ℂ} {r : ℝ} (hr : 0 < r) (hr8 : r ≤ 1/8)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hw : ‖w‖=1) {k : ℕ} (hk : 2 ≤ k) :
    ‖A‖^k+r^k*‖B‖^k ≤ 3*(‖A^k+(r:ℂ)^k*B^k‖+
      |(w*A^(k-1)+w*(r:ℂ)^k*B^(k-1)).re|+
      |(w*A^(k-1)).im|+|(w*(r:ℂ)^k*B^(k-1)).im|) := by
  let C := w*A^(k-1)
  let D := w*(r:ℂ)^k*B^(k-1)
  have hC : ‖C‖=‖A‖^(k-1) := by simp [C,norm_pow,hw]
  have hD : ‖D‖=r^k*‖B‖^(k-1) := by simp [D,norm_pow,hw,Complex.norm_real,abs_of_pos hr]
  have hpow (z : ℝ) : z^(k-1)*z=z^k := by rw [← pow_succ,Nat.sub_add_cancel (by omega)]
  by_cases hsmall : ‖D‖ ≤ ‖C‖/2
  · have hca := complex_coefficient_norm_le C D
    have hW : ‖A‖^k+r^k*‖B‖^k ≤ ‖C‖+‖D‖ := by
      rw [hC,hD]
      apply add_le_add
      · rw [← hpow ‖A‖]
        exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg A) _) hA
      · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr.le k)
        rw [← hpow ‖B‖]
        exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg B) _) hB
    change ‖A‖^k+r^k*‖B‖^k ≤ 3*(‖A^k+(r:ℂ)^k*B^k‖+|(C+D).re|+|C.im|+|D.im|)
    nlinarith [norm_nonneg (A^k+(r:ℂ)^k*B^k),abs_nonneg D.im]
  · have hcomp : ‖A‖^(k-1) ≤ 2*r^k*‖B‖^(k-1) := by rw [←hC,mul_assoc,←hD]; linarith
    have hbig := coupled_power_comparison (norm_nonneg A) (norm_nonneg B) hr.le
      (by linarith : r≤1) hk hcomp
    have hF : r^k*‖B‖^k-‖A‖^k ≤ ‖A^k+(r:ℂ)^k*B^k‖ := by
      have hh := norm_sub_norm_le ((r:ℂ)^k*B^k) (-A^k)
      simpa only [sub_neg_eq_add,add_comm,norm_neg,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hr] using hh
    have hquarter : ‖A‖^k ≤ (r^k*‖B‖^k)/2 := by
      have hn : 0 ≤ r^k*‖B‖^k := by positivity
      nlinarith
    have hn1 := abs_nonneg (w*A^(k-1)+w*(r:ℂ)^k*B^(k-1)).re
    have hn2 := abs_nonneg (w*A^(k-1)).im
    have hn3 := abs_nonneg (w*(r:ℂ)^k*B^(k-1)).im
    nlinarith
end


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
attribute [local instance] OAI.YauCounterexamples.threeNoncancelNormedSpace
local instance threeNoncancelContinuousSMul_r38d1c7_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeCoupled_direction_norm (r : ℝ) (k : ℕ) (p : ThreeManifold) (v : ThreeModel) (hv : ‖v‖≤1) :
    |fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0 v| ≤
      ‖fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0‖ := by
  have h := (fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0).le_opNorm v
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _) hv)
lemma product_coefficient_bound {K L u x h : ℝ} (hK : 0<K) (_hL : 0≤L)
    (hx : |x|≤1) (hh : |K*(h-x*u)|≤L) : |h|≤L/K+|u| := by
  have ha : |h-x*u|≤L/K := by
    apply (le_div_iff₀ hK).mpr
    simpa only [abs_mul,abs_of_pos hK,mul_comm] using hh
  have hb : |x*u|≤|u| := by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg u) hx
  have hc := abs_add_le (h-x*u) (x*u)
  simp only [sub_add_cancel] at hc
  linarith
lemma threeCoupled_sprite_bounds (r : ℝ) (k : ℕ) (hk : 1≤k) (p : ThreeManifold) :
    let C := (p.2:ℂ)^k*productA p.1^(k-1)
    let D := (p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)
    let L := ‖fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0‖
    |(C+D).re| ≤ L/(k:ℝ)+|threeCoupled r k p| ∧
    |C.im| ≤ L/(k:ℝ)+|threeCoupled r k p| ∧
    |D.im| ≤ L/(k:ℝ)+|threeCoupled r k p| := by
  dsimp only
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hh (i : Fin 3) := threeCoupled_direction_norm r k p (threeSphereDirection p i) (threeSphereDirection_norm p i)
  simp_rw [threeCoupled_sphere_direction r k hk p] at hh
  have h0 := product_coefficient_bound hk' (norm_nonneg _) (productAxis_coord_le p.1 0) (hh 0)
  have h1 := product_coefficient_bound hk' (norm_nonneg _) (productAxis_coord_le p.1 1) (hh 1)
  have h2 := product_coefficient_bound hk' (norm_nonneg _) (productAxis_coord_le p.1 2) (hh 2)
  norm_num [productA_axis,productB_axis,Fin.ext_iff] at h0 h1 h2
  refine ⟨h0, ?_, ?_⟩
  · simpa only [Complex.mul_re,Complex.mul_im,←neg_add,abs_neg,add_comm] using h1
  · simpa only [Complex.mul_re,Complex.mul_im,←neg_add,abs_neg,add_comm] using h2
lemma threeCoupled_value_bound (r : ℝ) (k : ℕ) (hk : 1≤k) (p : ThreeManifold) :
    ‖(productA p.1)^k+(r:ℂ)^k*(productB p.1)^k‖ ≤ |threeCoupled r k p|+
      ‖fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0‖/(k:ℝ) := by
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hi := threeCoupled_direction_norm r k p (threeCircleDirection p) (threeCircleDirection_norm p)
  rw [threeCoupled_circle_direction r k hk p,abs_mul,abs_neg,abs_of_pos hk'] at hi
  have him : |(threeCoupledComplex r k p).im|≤‖fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0‖/(k:ℝ) := by
    apply (le_div_iff₀ hk').mpr
    simpa only [mul_comm] using hi
  have hc := Complex.norm_le_abs_re_add_abs_im (threeCoupledComplex r k p)
  have hn : ‖threeCoupledComplex r k p‖=‖(productA p.1)^k+(r:ℂ)^k*(productB p.1)^k‖ := by
    simp only [threeCoupledComplex,norm_mul,norm_pow,p.2.norm_coe,one_pow,mul_one]
  rw [hn] at hc
  exact hc.trans (add_le_add (le_refl _) him)

theorem threeCoupled_global_noncancellation_oai {r : ℝ} (hr : 0 < r) (hr8 : r≤1/8)
    (k : ℕ) (hk : 2≤k) (p : ThreeManifold) :
    productWeight r k p ≤ 12*(|threeCoupled r k p|+
      ‖fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0‖/(k:ℝ)) := by
  have hw : ‖(p.2:ℂ)^k‖=1 := by simp only [norm_pow,p.2.norm_coe,one_pow]
  have hh := coupled_power_uniform_bound hr hr8 (productA_norm_le p.1) (productB_norm_le p.1) hw hk
  have hcoeff := threeCoupled_sprite_bounds r k (by omega : 1≤k) p
  have hval := threeCoupled_value_bound r k (by omega : 1≤k) p
  dsimp only at hcoeff
  unfold productWeight
  linarith [hcoeff.1,hcoeff.2.1,hcoeff.2.2]

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.threeCoupled_global_noncancellation_oai := @OAI.YauCounterexamples.threeCoupled_global_noncancellation_oai
