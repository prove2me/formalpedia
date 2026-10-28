-- Prove2me | solution 1 for OAI.YauCounterexamples.threeLogEnvelope_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:32:02.970563+00:00
-- url     : https://prove2.me/submissions/f4493046-30f5-4b95-a3de-0c37f00f5077

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ScalarLogFirst
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma scalarLog_first {q : E → ℝ} {x : E} (hq : DifferentiableAt ℝ q x) (hx : q x ≠ 0) (v : E) :
    fderiv ℝ (fun y => Real.log (q y)) x v = (q x)⁻¹*fderiv ℝ q x v := by
  rw [(hq.hasFDerivAt.log hx).fderiv]
  rfl
lemma scalarLog_second {q : E → ℝ} (hq : ContDiff ℝ ∞ q) {x : E} (hx : q x ≠ 0) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (q y))) x v w =
      (q x)⁻¹*fderiv ℝ (fderiv ℝ q) x v w - (q x)⁻¹^2*fderiv ℝ q x v*fderiv ℝ q x w := by
  have he : (fun y => fderiv ℝ (fun z => Real.log (q z)) y) =ᶠ[𝓝 x]
      (fun y => (q y)⁻¹ • fderiv ℝ q y) := by
    filter_upwards [hq.continuous.continuousAt.eventually_ne hx] with y hy
    exact ((hq.differentiable (by simp) y).hasFDerivAt.log hy).fderiv
  rw [he.fderiv_eq]
  have hi := (hasFDerivAt_inv hx).comp x (hq.differentiable (by simp) x).hasFDerivAt
  have hD := ((hq.fderiv_right (m:=∞) (by simp)).differentiable (by simp) x).hasFDerivAt
  change fderiv ℝ ((((fun t : ℝ => t⁻¹) ∘ q) • fderiv ℝ q)) x v w = _
  rw [(hi.smul hD).fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,Function.comp_apply,inv_pow,smul_eq_mul]
  ring
lemma directional_clm_comp_general {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : E →L[ℝ] F) {f : F → V}
    (hf : Differentiable ℝ f) (x v : E) :
    fderiv ℝ (f ∘ L) x v = fderiv ℝ f (L x) (L v) := by
  rw [fderiv_comp x (hf _) L.differentiableAt,L.fderiv]
  rfl
lemma second_clm_comp_general {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : E →L[ℝ] F) {f : F → V}
    (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (f ∘ L) y w) x v =
      fderiv ℝ (fun y => fderiv ℝ f y (L w)) (L x) (L v) := by
  simp_rw [directional_clm_comp_general L (hf.differentiable (by simp))]
  exact directional_clm_comp_general L
    (((hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)) x v
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
section StereoJets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma stereoAux_directional (v x w : E) :
    fderiv ℝ (stereoInvFunAux v) x w =
      (‖x‖^2+4)⁻¹ • ((4:ℝ) • w + (2 * inner ℝ x w) • v) -
      ((‖x‖^2+4)⁻¹ ^2 * (2 * inner ℝ x w)) •
        ((4:ℝ) • x + (‖x‖^2-4) • v) := by
  have hn : HasFDerivAt (fun y : E => ‖y‖^2) ((2:ℝ) • innerSL ℝ x) x := by
    simpa only [two_smul] using (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hi := (hasFDerivAt_inv (by positivity : ‖x‖^2+4 ≠ 0)).comp x (hn.add_const 4)
  have hp := ((hasFDerivAt_id x).const_smul (4:ℝ)).add ((hn.sub_const 4).smul_const v)
  have hh := hi.smul hp
  change HasFDerivAt (stereoInvFunAux v) _ x at hh
  rw [hh.fderiv]
  simp only [_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
    smul_eq_mul]
  simp [Function.comp_apply,ContinuousLinearMap.comp_apply,smul_add,smul_smul,inv_pow,sub_eq_add_neg]
  module

theorem stereoAux_second_jet (v w : E) :
    HasFDerivAt (fun x : E => fderiv ℝ (stereoInvFunAux v) x w)
      ((innerSL ℝ w).smulRight v) 0 := by
  have hn : HasFDerivAt (fun y : E => ‖y‖^2) (0 : E →L[ℝ] ℝ) 0 := by
    convert (hasStrictFDerivAt_norm_sq (0:E)).hasFDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hi := (hasFDerivAt_inv (by norm_num : ‖(0:E)‖^2+4 ≠ 0)).comp (0:E) (hn.add_const 4)
  have ht := ((innerSL ℝ w).hasFDerivAt (x := (0:E))).const_mul 2
  have ht' : HasFDerivAt (fun x : E => 2 * inner ℝ x w) ((2:ℝ) • innerSL ℝ w) 0 := by
    simpa only [innerSL_apply_apply,real_inner_comm] using ht
  have hp := ((hasFDerivAt_id (0:E)).const_smul (4:ℝ)).add ((hn.sub_const 4).smul_const v)
  have hq := hi.smul ((hasFDerivAt_const ((4:ℝ) • w) (0:E)).add (ht'.smul_const v))
  have hr := ((hi.pow 2).mul ht').smul hp
  convert hq.sub hr using 1
  · funext x
    exact stereoAux_directional v x w
  · ext z
    simp only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add,
      inner_zero_left,innerSL_apply_apply,_root_.add_apply,
      _root_.sub_apply,_root_.smul_apply,
      ContinuousLinearMap.smulRight_apply,_root_.zero_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul ]
    norm_num [smul_add,smul_smul]
    module
end StereoJets
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

lemma roundChart_directional (p : E) (L : F →ₗᵢ[ℝ] E) (x w : F) :
    fderiv ℝ (roundChart p L) x w = fderiv ℝ (stereoInvFunAux (-p)) (L x) (L w) := by
  rw [show roundChart p L = stereoInvFunAux (-p) ∘ L.toContinuousLinearMap from rfl,
    fderiv_comp x ((contDiff_stereoInvFunAux (m := ∞)).differentiable (by simp)).differentiableAt
      L.toContinuousLinearMap.differentiableAt]
  rw [ContinuousLinearMap.fderiv]
  rfl

lemma roundChart_second (p : E) (L : F →ₗᵢ[ℝ] E) (w : F) :
    HasFDerivAt (fun x => fderiv ℝ (roundChart p L) x w)
      ((innerSL ℝ w).smulRight (-p)) 0 := by
  have h : HasFDerivAt (fun x : E => fderiv ℝ (stereoInvFunAux (-p)) x (L w))
      ((innerSL ℝ (L w)).smulRight (-p)) (L.toContinuousLinearMap 0) := by
    simpa using stereoAux_second_jet (-p) (L w)
  have hh := h.comp (0:F) L.toContinuousLinearMap.hasFDerivAt
  convert hh using 1
  · funext x
    exact roundChart_directional p L x w
  · ext z
    simp

theorem roundChart_metric_first (p : E) (L : F →ₗᵢ[ℝ] E)
    (hL : ∀ w, inner ℝ p (L w) = 0) (v w : F) :
    HasFDerivAt (fun x => inner ℝ (fderiv ℝ (roundChart p L) x v)
      (fderiv ℝ (roundChart p L) x w)) (0 : F →L[ℝ] ℝ) 0 := by
  have hL' : ∀ z, inner ℝ (L z) p = 0 := fun z => (real_inner_comm _ _).trans (hL z)
  have hh := (roundChart_second p L v).inner ℝ (roundChart_second p L w)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp [fderivInnerCLM_apply, (roundChart_first p L).fderiv,
    ContinuousLinearMap.smulRight_apply,inner_smul_left,inner_smul_right,hL,hL']


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
lemma lpProductFunction_fderiv {f : E → A} {g : F → B}
    {x : WithLp 2 (E×F)} (hf : DifferentiableAt ℝ f x.fst) (hg : DifferentiableAt ℝ g x.snd) :
    fderiv ℝ (lpProductFunction f g) x = lpProductLinearMap (fderiv ℝ f x.fst) (fderiv ℝ g x.snd) :=
  (lpProductFunction_hasFDerivAt hf.hasFDerivAt hg.hasFDerivAt).fderiv
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
lemma lpProductFunction_metric {f : E → A} {g : F → B}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v w : WithLp 2 (E×F)) :
    inner ℝ (fderiv ℝ (lpProductFunction f g) x v) (fderiv ℝ (lpProductFunction f g) x w) =
      inner ℝ (fderiv ℝ f x.fst v.fst) (fderiv ℝ f x.fst w.fst) +
      inner ℝ (fderiv ℝ g x.snd v.snd) (fderiv ℝ g x.snd w.snd) := by
  rw [lpProductFunction_fderiv (hf.differentiable (by simp) _)
    (hg.differentiable (by simp) _)]
  simp [WithLp.prod_inner_apply]
lemma lpProductRoundChart_first (p : A) (q : B) (L : E →ₗᵢ[ℝ] A) (K : F →ₗᵢ[ℝ] B) :
    HasFDerivAt (lpProductFunction (roundChart p L) (roundChart q K))
      (lpProductIsometry L K).toContinuousLinearMap 0 := by
  exact lpProductFunction_hasFDerivAt (roundChart_first p L) (roundChart_first q K)
lemma lpProductRoundChart_metric_first (p : A) (q : B) (L : E →ₗᵢ[ℝ] A) (K : F →ₗᵢ[ℝ] B)
    (hL : ∀ w, inner ℝ p (L w) = 0) (hK : ∀ w, inner ℝ q (K w) = 0)
    (v w : WithLp 2 (E×F)) :
    HasFDerivAt (fun x => inner ℝ
      (fderiv ℝ (lpProductFunction (roundChart p L) (roundChart q K)) x v)
      (fderiv ℝ (lpProductFunction (roundChart p L) (roundChart q K)) x w))
      (0 : WithLp 2 (E×F) →L[ℝ] ℝ) 0 := by
  simp_rw [lpProductFunction_metric (roundChart_smooth _ _) (roundChart_smooth _ _)]
  have h₁ := (roundChart_metric_first p L hL v.fst w.fst).comp
    (0 : WithLp 2 (E×F)) (WithLp.fstL 2 ℝ E F).hasFDerivAt
  have h₂ := (roundChart_metric_first q K hK v.snd w.snd).comp
    (0 : WithLp 2 (E×F)) (WithLp.sndL 2 ℝ E F).hasFDerivAt
  convert h₁.add h₂ using 1 <;> try rfl
  ext x
  simp
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

lemma unitSphereFrame_inner (p : Metric.sphere (0 : A) 1) (a : A) (w : Euclidean n) :
    inner ℝ (unitSphereFrame (n:=n) p w) a = inner ℝ w (unitSphereCoordinates (n:=n) p a) := by
  rw [← (unitSphereFrame (n:=n) p).inner_map_map,unitSphereFrame_coordinates]
  have hh := unitSphereFrame_orthogonal p w
  rw [real_inner_comm] at hh
  simp [unitSphereProjection,inner_sub_right,inner_smul_right,hh]


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CoordinateForm
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
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma metricProfileTraceForm_apply (B H : CoordinateForm E) (a v : E) :
    metricProfileTraceForm B H a v v = B v v*H a a+(1+B a a)*H v v := by
  simp only [metricProfileTraceForm,add_apply,smul_apply,smul_eq_mul]
  ring

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

omit [FiniteDimensional ℝ E] in
lemma selfMetricFlat_apply (g : SmoothMetric E E) (x v w : E) :
    selfMetricFlat g x v w = g.inner x v w := rfl

lemma selfMetricFlat_invertible (g : SmoothMetric E E) (x : E) :
    (selfMetricFlat g x).IsInvertible := by
  rw [←localMetricFlat_self g x x]
  exact localMetricFlat_invertible g x x (mem_baseSet_trivializationAt E _ x)

lemma coordinateKoszul_apply (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (v w z : E) :
    coordinateKoszul D v w z = (D v w z+D w v z-D z v w)/2 := by
  change (1/2 : ℝ) * (D v w z+D w v z-D z v w) = _
  ring

lemma metricChristoffel_pairing (g : SmoothMetric E E) (x v w z : E) :
    selfMetricFlat g x (metricChristoffel g x v w) z =
      (fderiv ℝ (selfMetricFlat g) x v w z+fderiv ℝ (selfMetricFlat g) x w v z-
        fderiv ℝ (selfMetricFlat g) x z v w)/2 := by
  have h := (selfMetricFlat_invertible g x).inverse_apply_eq.mp
    (show (selfMetricFlat g x).inverse (coordinateKoszul (fderiv ℝ (selfMetricFlat g) x) v w) =
      metricChristoffel g x v w from rfl)
  exact (congrArg (fun l : E →L[ℝ] ℝ => l z) h.symm).trans (coordinateKoszul_apply _ _ _ _)


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FderivMetricPairing
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [FiniteDimensional ℝ E] in
lemma fderiv_metric_pairing (g : SmoothMetric E E) (x v w z : E) :
    fderiv ℝ (fun y => selfMetricFlat g y w z) x v =
      fderiv ℝ (selfMetricFlat g) x v w z := by
  have hd := (contDiff_selfMetricFlat g).differentiable (by simp)
  rw [fderiv_clm_apply ((hd x).clm_apply (differentiableAt_const w))
      (differentiableAt_const z), fderiv_clm_apply (hd x) (differentiableAt_const w)]
  simp

omit [FiniteDimensional ℝ E] in
lemma fderiv_fderiv_apply {F : E → V} (hF : ContDiff ℝ ∞ F) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ F y w) x v = fderiv ℝ (fderiv ℝ F) x v w := by
  rw [fderiv_clm_apply ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const w)]
  simp

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ActualCoordinateHessianApply
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
section ScalarHessian
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma actualCoordinateHessian_apply (g : SmoothMetric E E) (f : E → ℝ) (x v w : E) :
    actualCoordinateHessian g f x v w =
      fderiv ℝ (fderiv ℝ f) x v w - fderiv ℝ f x (metricChristoffel g x v w) := by
  rfl

omit [FiniteDimensional ℝ E] in
lemma fderiv_clm_comp_apply (L : V →L[ℝ] ℝ) {F : E → V}
    (hF : ContDiff ℝ ∞ F) (x v : E) :
    fderiv ℝ (fun y => L (F y)) x v = L (fderiv ℝ F x v) := by
  change (fderiv ℝ (L ∘ F) x) v = _
  rw [(L.hasFDerivAt.comp x ((hF.differentiable (by simp) x).hasFDerivAt)).fderiv]
  rfl

omit [FiniteDimensional ℝ E] in
lemma fderiv_second_clm_comp_apply (L : V →L[ℝ] ℝ) {F : E → V}
    (hF : ContDiff ℝ ∞ F) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => L (F y))) x v w =
      L (fderiv ℝ (fderiv ℝ F) x v w) := by
  have hLF : ContDiff ℝ ∞ (fun y => L (F y)) := L.contDiff.comp hF
  rw [← fderiv_fderiv_apply hLF]
  simp_rw [fderiv_clm_comp_apply L hF]
  rw [fderiv_clm_comp_apply L
    ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const),
    fderiv_fderiv_apply hF]

lemma actualCoordinateHessian_add (g : SmoothMetric E E) {f h : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (x v w : E) :
    actualCoordinateHessian g (fun y => f y + h y) x v w =
      actualCoordinateHessian g f x v w + actualCoordinateHessian g h x v w := by
  have hfd := hf.differentiable (by simp)
  have hhd := hh.differentiable (by simp)
  simp only [actualCoordinateHessian_apply]
  have he : fderiv ℝ (fun y => f y + h y) =
      fun y => fderiv ℝ f y + fderiv ℝ h y := by
    funext y
    exact fderiv_add (hfd y) (hhd y)
  rw [he, fderiv_fun_add
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    ((hh.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)]
  simp only [add_apply]
  ring

lemma actualCoordinateHessian_square (g : SmoothMetric E E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (x v w : E) :
    actualCoordinateHessian g (fun y => (f y)^2) x v w =
      2 * (fderiv ℝ f x v) * (fderiv ℝ f x w) +
      2 * f x * actualCoordinateHessian g f x v w := by
  have hfd := hf.differentiable (by simp)
  have hff : ContDiff ℝ ∞ (fun y => (f y)^2) := hf.pow 2
  have he (y z : E) : fderiv ℝ (fun s => (f s)^2) y z =
      2 * f y * fderiv ℝ f y z := by
    simp only [pow_two]
    rw [fderiv_fun_mul (hfd y) (hfd y)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [actualCoordinateHessian_apply, ← fderiv_fderiv_apply hff]
  simp_rw [he]
  have hdf : ContDiff ℝ ∞ (fun y => fderiv ℝ f y w) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [fderiv_fun_mul ((contDiff_const.mul hf).differentiable (by simp) x)
      (hdf.differentiable (by simp) x),
    fderiv_fun_mul (differentiableAt_const _) (hfd x)]
  simp only [add_apply, smul_apply, smul_eq_mul, fderiv_const_apply, zero_apply]
  rw [fderiv_fderiv_apply hf, actualCoordinateHessian_apply]
  ring

end ScalarHessian

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
attribute [local instance] OAI.YauCounterexamples.threeModelNormedSpace
local instance threeModelContinuousSMul_r5758ad_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
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
end


open Set Filter Manifold Bundle Function
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
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeRadiusNormedSpace
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
local instance threeChartContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul

attribute [local instance] OAI.YauCounterexamples.threeChartNormedSpace
lemma threeChartMetric_selfFlat (g : SmoothMetric ThreeModel ThreeManifold) (p : ThreeManifold) (y : ThreeModel) :
    selfMetricFlat (threeChartMetric g p) y = chartMetricForm g p y := by
  ext v w
  rw [selfMetricFlat_apply]
  rfl
lemma threeChartMetric_background (p : ThreeManifold) (y v w : ThreeModel) :
    selfMetricFlat (threeChartMetric threeBackgroundMetric p) y v w =
      inner ℝ (fderiv ℝ (threeChartMap p) y v) (fderiv ℝ (threeChartMap p) y w) := by
  rw [threeChartMetric_selfFlat,chartMetricForm_pairing]
  change (inner ℝ : ThreeAmbient → ThreeAmbient → ℝ) (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion _ _) _ = _
  exact congrArg₂ (inner ℝ : ThreeAmbient → ThreeAmbient → ℝ) (three_coordinate_embedding p y v) (three_coordinate_embedding p y w)
lemma threeChartMetric_background_zero (p : ThreeManifold) :
    selfMetricFlat (threeChartMetric threeBackgroundMetric p) 0 = (innerSL ℝ : ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ) := by
  ext v w
  have hh : fderiv ℝ (threeChartMap p) 0 = (threeFrame p).toContinuousLinearMap :=
    (lpProductRoundChart_first (p.1:Euclidean 3) (p.2:ℂ) (sphereFrame p.1) (unitSphereFrame (n:=1) p.2)).fderiv
  rw [threeChartMetric_background,hh]
  exact (threeFrame p).inner_map_map _ _
lemma threeChartMetric_background_first (p : ThreeManifold) :
    fderiv ℝ (selfMetricFlat (threeChartMetric threeBackgroundMetric p)) 0 = 0 := by
  ext v w z
  rw [←fderiv_metric_pairing]
  simp_rw [threeChartMetric_background]
  exact congrArg (fun L : ThreeModel →L[ℝ] ℝ => L v)
    (lpProductRoundChart_metric_first (p.1:Euclidean 3) (p.2:ℂ)
      (sphereFrame p.1) (unitSphereFrame (n:=1) p.2)
      (sphereFrame_orthogonal p.1) (unitSphereFrame_orthogonal (n:=1) p.2) w z).fderiv
lemma threeChartMetric_background_Christoffel (p : ThreeManifold) :
    metricChristoffel (threeChartMetric threeBackgroundMetric p) 0 = 0 := by
  ext v w
  apply (selfMetricFlat_invertible (threeChartMetric threeBackgroundMetric p) 0).injective
  ext z
  rw [metricChristoffel_pairing,threeChartMetric_background_first]
  simp
lemma threeChartMetric_background_hessian (p : ThreeManifold) (f : ThreeModel → ℝ) :
    actualCoordinateHessian (threeChartMetric threeBackgroundMetric p) f 0 =
      fderiv ℝ (fderiv ℝ f) 0 := by
  simp [actualCoordinateHessian,coordinateCovariantSecond,threeChartMetric_background_Christoffel]
end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
local instance threeRadiusContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeRadiusEuclideanContinuousSMul (dimension : ℕ) : ContinuousSMul ℝ (Euclidean dimension) :=
  IsBoundedSMul.continuousSMul
local instance threeRadius_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩

attribute [local instance] OAI.YauCounterexamples.threeRadiusNormedSpace
lemma threeSphereMap_smooth (p : ThreeManifold) : ContDiff ℝ ∞ (threeSphereMap p) :=
  (roundChart_smooth _ _).comp (WithLp.fstL 2 ℝ (Euclidean 2) (Euclidean 1)).contDiff
lemma threeSphereMap_zero (p : ThreeManifold) : threeSphereMap p 0 = (p.1 : Euclidean 3) := by
  simp [threeSphereMap,Function.comp_apply,roundChart_zero]
lemma threeSphereMap_first (p : ThreeManifold) (v : ThreeModel) :
    fderiv ℝ (threeSphereMap p) 0 v = sphereFrame p.1 v.fst := by
  rw [threeSphereMap,directional_clm_comp_general _ ((roundChart_smooth _ _).differentiable (by simp))]
  change fderiv ℝ (roundChart (p.1:Euclidean 3) (sphereFrame p.1)) 0 v.fst = _
  rw [(roundChart_first _ _).fderiv]
  rfl
lemma threeSphereMap_second (p : ThreeManifold) (v w : ThreeModel) :
    fderiv ℝ (fderiv ℝ (threeSphereMap p)) 0 v w =
      -inner ℝ v.fst w.fst • (p.1:Euclidean 3) := by
  rw [←fderiv_fderiv_apply (threeSphereMap_smooth p)]
  rw [threeSphereMap,second_clm_comp_general _ (roundChart_smooth _ _)]
  change fderiv ℝ (fun y => fderiv ℝ (roundChart (p.1:Euclidean 3) (sphereFrame p.1)) y w.fst) 0 v.fst = _
  rw [(roundChart_second _ _ _).fderiv]
  simp [real_inner_comm,smul_neg,neg_smul]

lemma threeSphereCoord_smooth (p : ThreeManifold) (i : Fin 3) :
    ContDiff ℝ ∞ (threeSphereCoord p i) := (innerSL ℝ (productAxis i)).contDiff.comp (threeSphereMap_smooth p)
lemma threeSphereCoord_zero (p : ThreeManifold) (i : Fin 3) :
    threeSphereCoord p i 0 = (p.1:Euclidean 3) i := by
  rw [threeSphereCoord,threeSphereMap_zero,productAxis_coord]
lemma threeSphereCoord_first (p : ThreeManifold) (i : Fin 3) (v : ThreeModel) :
    fderiv ℝ (threeSphereCoord p i) 0 v = inner ℝ (threeSphereDirection p i) v := by
  rw [show threeSphereCoord p i = fun y => (innerSL ℝ (productAxis i)) (threeSphereMap p y) from rfl]
  rw [fderiv_clm_comp_apply _ (threeSphereMap_smooth p),threeSphereMap_first]
  change inner ℝ (productAxis i) (unitSphereFrame (n:=2) p.1 v.fst)=_
  rw [real_inner_comm,unitSphereFrame_inner,real_inner_comm]
  simp [threeSphereDirection,WithLp.prod_inner_apply]
lemma threeSphereCoord_second (p : ThreeManifold) (i : Fin 3) (v w : ThreeModel) :
    fderiv ℝ (fderiv ℝ (threeSphereCoord p i)) 0 v w =
      -(p.1:Euclidean 3) i * inner ℝ v.fst w.fst := by
  rw [show threeSphereCoord p i = fun y => (innerSL ℝ (productAxis i)) (threeSphereMap p y) from rfl]
  rw [fderiv_second_clm_comp_apply _ (threeSphereMap_smooth p),threeSphereMap_second]
  simp [inner_smul_right,productAxis_coord,mul_comm]

lemma threeRadiusSq_smooth (p : ThreeManifold) : ContDiff ℝ ∞ (threeRadiusSq p) :=
  ((threeSphereCoord_smooth p 0).pow 2).add ((threeSphereCoord_smooth p 1).pow 2)
lemma threeRadiusSq_zero (p : ThreeManifold) : threeRadiusSq p 0 =
    (p.1:Euclidean 3) 0^2+(p.1:Euclidean 3) 1^2 := by
  simp [threeRadiusSq,threeSphereCoord_zero]
lemma threeRadiusSq_first (p : ThreeManifold) (v : ThreeModel) :
    fderiv ℝ (threeRadiusSq p) 0 v =
      2*(p.1:Euclidean 3) 0*inner ℝ (threeSphereDirection p 0) v+
      2*(p.1:Euclidean 3) 1*inner ℝ (threeSphereDirection p 1) v := by
  have h0 := ((threeSphereCoord_smooth p 0).differentiable (by simp) (0:ThreeModel)).hasFDerivAt.pow 2
  have h1 := ((threeSphereCoord_smooth p 1).differentiable (by simp) (0:ThreeModel)).hasFDerivAt.pow 2
  have hh : HasFDerivAt (threeRadiusSq p) _ 0 := h0.add h1
  rw [hh.fderiv]
  simp [threeSphereCoord_zero,threeSphereCoord_first]
lemma threeRadiusSq_second (p : ThreeManifold) (v w : ThreeModel) :
    fderiv ℝ (fderiv ℝ (threeRadiusSq p)) 0 v w =
      2*(inner ℝ (threeSphereDirection p 0) v*inner ℝ (threeSphereDirection p 0) w+
        inner ℝ (threeSphereDirection p 1) v*inner ℝ (threeSphereDirection p 1) w)-
      2*threeRadiusSq p 0*inner ℝ v.fst w.fst := by
  rw [←threeChartMetric_background_hessian p]
  change actualCoordinateHessian (threeChartMetric threeBackgroundMetric p)
    (fun y => threeSphereCoord p 0 y^2+threeSphereCoord p 1 y^2) 0 v w = _
  rw [actualCoordinateHessian_add _ ((threeSphereCoord_smooth p 0).pow 2) ((threeSphereCoord_smooth p 1).pow 2)]
  rw [actualCoordinateHessian_square _ (threeSphereCoord_smooth p 0),actualCoordinateHessian_square _ (threeSphereCoord_smooth p 1)]
  rw [threeChartMetric_background_hessian,threeChartMetric_background_hessian,
    threeSphereCoord_first,threeSphereCoord_first,threeSphereCoord_first,threeSphereCoord_first,
    threeSphereCoord_second,threeSphereCoord_second,threeSphereCoord_zero,threeSphereCoord_zero,threeRadiusSq_zero]
  ring

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ThreeLogNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
local instance threeLog_dimension_fact_r5758ad_1 (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
lemma threeSphereDirection_inner (p : ThreeManifold) (i j : Fin 3) :
    inner ℝ (threeSphereDirection p i) (threeSphereDirection p j) =
      (if i=j then 1 else 0)-(p.1:Euclidean 3) i*(p.1:Euclidean 3) j := by
  simp only [threeSphereDirection,WithLp.prod_inner_apply,
    inner_zero_left,add_zero,unitSphereCoordinates_inner]
  have hi : inner ℝ (p.1:Euclidean 3) (productAxis i) = (p.1:Euclidean 3) i := by rw [real_inner_comm,productAxis_coord]
  have hj : inner ℝ (p.1:Euclidean 3) (productAxis j) = (p.1:Euclidean 3) j := by rw [real_inner_comm,productAxis_coord]
  rw [hi,hj,productAxis_coord]
  simp [productAxis,PiLp.single_apply]
lemma threeSphereDirection_fst_inner (p : ThreeManifold) (i j : Fin 3) :
    inner ℝ (threeSphereDirection p i).fst (threeSphereDirection p j).fst =
      (if i=j then 1 else 0)-(p.1:Euclidean 3) i*(p.1:Euclidean 3) j := by
  have h:=threeSphereDirection_inner p i j
  simpa [threeSphereDirection,WithLp.prod_inner_apply] using h

attribute [local instance] OAI.YauCounterexamples.threeLogNormedSpace
local instance threeLogContinuousSMul_r5758ad_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeLogEnvelope_first (p : ThreeManifold) (c : ℝ) (hq : threeRadiusSq p 0 ≠ 0) (v : ThreeModel) :
    fderiv ℝ (threeLogEnvelope p c) 0 v =
      (c/2)*(threeRadiusSq p 0)⁻¹*fderiv ℝ (threeRadiusSq p) 0 v := by
  change fderiv ℝ ((c/2) • (fun y => Real.log (threeRadiusSq p y))) 0 v = _
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply,smul_apply,smul_eq_mul]
  rw [scalarLog_first ((threeRadiusSq_smooth p).differentiable (by simp) 0) hq]
  ring
lemma threeLogEnvelope_second (p : ThreeManifold) (c : ℝ) (hq : threeRadiusSq p 0 ≠ 0) (v w : ThreeModel) :
    fderiv ℝ (fderiv ℝ (threeLogEnvelope p c)) 0 v w =
      (c/2)*((threeRadiusSq p 0)⁻¹*fderiv ℝ (fderiv ℝ (threeRadiusSq p)) 0 v w-
        (threeRadiusSq p 0)⁻¹^2*fderiv ℝ (threeRadiusSq p) 0 v*fderiv ℝ (threeRadiusSq p) 0 w) := by
  change fderiv ℝ (fderiv ℝ ((c/2) • (fun y => Real.log (threeRadiusSq p y)))) 0 v w = _
  rw [fderiv_const_smul_field]
  rw [fderiv_const_smul_field (𝕜:=ℝ) (f:=fderiv ℝ (fun y => Real.log (threeRadiusSq p y))) (c/2)]
  simp only [Pi.smul_apply,smul_apply,smul_eq_mul]
  rw [scalarLog_second (threeRadiusSq_smooth p) hq]

lemma threeLogEnvelope_first_axis (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) :
    fderiv ℝ (threeLogEnvelope p c) 0 = innerSL ℝ ((c/(p.1:Euclidean 3) 0) • threeSphereDirection p 0) := by
  have hq : threeRadiusSq p 0 ≠ 0 := by simp [threeRadiusSq_zero,hy,pow_ne_zero 2 hx]
  ext v
  rw [threeLogEnvelope_first p c hq,threeRadiusSq_first]
  simp only [threeRadiusSq_zero,hy,add_zero,mul_zero,zero_mul,innerSL_apply_apply,real_inner_smul_left]
  field_simp [hx]
  ring

lemma threeLogEnvelope_hessian_axis (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) (v w : ThreeModel) :
    actualCoordinateHessian (threeChartMetric threeBackgroundMetric p) (threeLogEnvelope p c) 0 v w =
      c/((p.1:Euclidean 3) 0)^2 *
        (inner ℝ (threeSphereDirection p 1) v*inner ℝ (threeSphereDirection p 1) w-
        inner ℝ (threeSphereDirection p 0) v*inner ℝ (threeSphereDirection p 0) w)-
      c*inner ℝ v.fst w.fst := by
  have hq : threeRadiusSq p 0 ≠ 0 := by simp [threeRadiusSq_zero,hy,pow_ne_zero 2 hx]
  rw [threeChartMetric_background_hessian,threeLogEnvelope_second p c hq,
    threeRadiusSq_second,threeRadiusSq_first,threeRadiusSq_first]
  simp only [threeRadiusSq_zero,hy,add_zero,mul_zero,zero_mul]
  field_simp [hx]
  ring

lemma threeLogEnvelope_gradient (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) :
    coordinateMetricGradient (threeChartMetric threeBackgroundMetric p) (threeLogEnvelope p c) 0 =
      (c/(p.1:Euclidean 3) 0) • threeSphereDirection p 0 := by
  apply (selfMetricFlat_invertible (threeChartMetric threeBackgroundMetric p) 0).inverse_apply_eq.mpr
  rw [threeChartMetric_background_zero,threeLogEnvelope_first_axis p c hx hy]
lemma threeLogEnvelope_trace_oai (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) :
    actualProfileTraceForm (threeChartMetric threeBackgroundMetric p) (threeLogEnvelope p c) 0
      (threeSphereDirection p 1) (threeSphereDirection p 1) =
      c*(1-c^2)*(1-((p.1:Euclidean 3) 0)^2)/((p.1:Euclidean 3) 0)^2 := by
  rw [actualProfileTraceForm,threeLogEnvelope_gradient p c hx hy,
    threeChartMetric_background_zero,metricProfileTraceForm_apply]
  simp only [ContinuousLinearMap.map_smul,smul_apply,smul_eq_mul]
  rw [threeLogEnvelope_hessian_axis p c hx hy,threeLogEnvelope_hessian_axis p c hx hy]
  have hi (v w : ThreeModel) : (innerSL ℝ v) w = inner ℝ v w := rfl
  simp only [hi,threeSphereDirection_inner,threeSphereDirection_fst_inner,hy]
  norm_num
  field_simp [hx]
  ring
end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.threeLogEnvelope_trace_oai := @OAI.YauCounterexamples.threeLogEnvelope_trace_oai
