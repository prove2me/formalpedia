-- Prove2me | solution 1 for OAI.YauCounterexamples.threeCoupled_global_residual_rapid_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:29:00.173563+00:00
-- url     : https://prove2.me/submissions/60eb04d6-cb02-43ac-9a65-a363569ec9a8

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_productSphere_power_trace
import Theorems.Thm_OAI_YauCounterexamples_threeCoupled_dominated_residual_rapid_decay

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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma fderiv_real_part {f : F → ℂ} {x : F} (hf : DifferentiableAt ℝ f x) (v : F) :
    fderiv ℝ (fun y => (f y).re) x v = (fderiv ℝ f x v).re := by
  have hh := Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt
  convert! congrArg (fun D => D v) hh.fderiv using 1
  all_goals try with_reducible_and_instances rfl

lemma second_real_part {f : F → ℂ} (hf : ContDiff ℝ ∞ f) (x v w : F) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => (f z).re) y w) x v =
      (fderiv ℝ (fun y => fderiv ℝ f y w) x v).re := by
  simp_rw [fderiv_real_part (hf.differentiable (by simp) _)]
  apply fderiv_real_part
  exact (((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)) x




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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SobolevRepresentativeOrderCongr
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma second_fderiv_const_mul_at (d : ℂ) {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => d * u z) y b) x a =
      d * fderiv ℝ (fun y => fderiv ℝ u y b) x a := by
  have he : (fun y => fderiv ℝ (fun z => d * u z) y b) =ᶠ[𝓝 x]
      (fun y => d * fderiv ℝ u y b) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    erw [fderiv_const_mul (hy.differentiableAt (by norm_num)) d]
    rfl
  rw [he.fderiv_eq]
  have hdu := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
    (differentiableAt_const b)
  erw [fderiv_const_mul hdu d]
  rfl

lemma euclideanElliptic_const_mul_at (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (d : ℂ) {u : E → ℂ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    euclideanElliptic b a c (fun y => d * u y) x = d * euclideanElliptic b a c u x := by
  simp only [euclideanElliptic, second_fderiv_const_mul_at d hu]
  erw [fderiv_const_mul (hu.differentiableAt (by norm_num)) d]
  simp only [_root_.smul_apply, smul_eq_mul, mul_left_comm _ d,
    ← Finset.mul_sum, ← mul_add]


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped SchwartzMap BoundedContinuousFunction



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
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma contMDiff_const_mul_complex {u : M → ℂ}
    {n : ℕ∞ω} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) n u) (c : ℂ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) n (fun x => c * u x) :=
  ((ContinuousLinearMap.mul ℝ ℂ) c).contMDiff.comp hu

lemma complexLaplaceBeltrami_const_mul {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u) (c : ℂ) (g : SmoothMetric E M) (x : M) :
    complexLaplaceBeltrami g (fun y => c * u y) x = c * complexLaplaceBeltrami g u x := by
  erw [complexLaplaceBeltrami_inChart (contMDiff_const_mul_complex hu c) g x
      (mem_chart_source E x), complexLaplaceBeltrami_inChart hu g x (mem_chart_source E x)]
  exact euclideanElliptic_const_mul_at _ _ _ c
    (contDiffAt_complex_inChart hu x (mem_chart_source E x))


end

open Set Filter Manifold
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer
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
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M] in
lemma complexLaplaceBeltrami_ofReal (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    complexLaplaceBeltrami g (fun y => (u y : ℂ)) x = (laplaceBeltrami g u x : ℂ) := by
  apply Complex.ext
  · rfl
  · exact laplaceBeltrami_zero g x

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ZeroJetProd
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
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {x : E}

lemma zero_jet_prod (f : ι → E → ℝ) (hf : ∀ i, HasFDerivAt (f i) (0 : E →L[ℝ] ℝ) x) :
    HasFDerivAt (fun y => ∏ i, f i y) (0 : E →L[ℝ] ℝ) x := by
  simpa using HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => hf i)

omit [DecidableEq ι] in
lemma zero_jet_sum (f : ι → E → ℝ) (hf : ∀ i, HasFDerivAt (f i) (0 : E →L[ℝ] ℝ) x) :
    HasFDerivAt (fun y => ∑ i, f i y) (0 : E →L[ℝ] ℝ) x := by
  simpa using HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hf i)

lemma zero_jet_det (A : E → Matrix ι ι ℝ)
    (hA : ∀ i j, HasFDerivAt (fun y => A y i j) (0 : E →L[ℝ] ℝ) x) :
    HasFDerivAt (fun y => (A y).det) (0 : E →L[ℝ] ℝ) x := by
  simp only [Matrix.det_apply']
  apply zero_jet_sum
  intro σ
  simpa using (zero_jet_prod (fun i y => A y (σ i) i) (fun i => hA (σ i) i)).const_mul (Equiv.Perm.sign σ : ℝ)

lemma zero_jet_adjugate (A : E → Matrix ι ι ℝ)
    (hA : ∀ i j, HasFDerivAt (fun y => A y i j) (0 : E →L[ℝ] ℝ) x) (i j : ι) :
    HasFDerivAt (fun y => (A y).adjugate i j) (0 : E →L[ℝ] ℝ) x := by
  simp only [Matrix.adjugate_apply]
  apply zero_jet_det
  intro k l
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact hasFDerivAt_const _ _
  · exact hA _ _

lemma zero_jet_inverse (A : E → Matrix ι ι ℝ)
    (hA : ∀ i j, HasFDerivAt (fun y => A y i j) (0 : E →L[ℝ] ℝ) x)
    (hn : (A x).det ≠ 0) (i j : ι) :
    HasFDerivAt (fun y => (A y)⁻¹ i j) (0 : E →L[ℝ] ℝ) x := by
  have hi := (hasFDerivAt_inv hn).comp x (zero_jet_det A hA)
  have hh := hi.mul (zero_jet_adjugate A hA i j)
  convert! hh using 1
  · funext y
    simp [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  · simp

lemma zero_jet_density (A : E → Matrix ι ι ℝ)
    (hA : ∀ i j, HasFDerivAt (fun y => A y i j) (0 : E →L[ℝ] ℝ) x)
    (hn : (A x).det ≠ 0) :
    HasFDerivAt (fun y => Real.sqrt (A y).det) (0 : E →L[ℝ] ℝ) x := by
  simpa using (zero_jet_det A hA).sqrt hn

lemma zero_jet_density_inverse (A : E → Matrix ι ι ℝ)
    (hA : ∀ i j, HasFDerivAt (fun y => A y i j) (0 : E →L[ℝ] ℝ) x)
    (hn : (A x).det ≠ 0) (i j : ι) :
    HasFDerivAt (fun y => Real.sqrt (A y).det * (A y)⁻¹ i j) (0 : E →L[ℝ] ℝ) x := by
  convert! (zero_jet_density A hA hn).mul (zero_jet_inverse A hA hn i j) using 1
  all_goals try with_reducible_and_instances rfl
  simp
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
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
section MetricLocality
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma laplaceBeltrami_metric_congr_nhds (g g' : SmoothMetric E M) (u : M → ℝ) {x : M}
    (he : ∀ᶠ z in 𝓝 x, ∀ v w : TangentSpace 𝓘(ℝ,E) z, g.inner z v w = g'.inner z v w) :
    laplaceBeltrami g u x = laplaceBeltrami g' u x := by
  let c := chartAt E x
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have ht : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv (mem_chart_source E x)] using (c.continuousAt_symm hx).tendsto
  have hc : metricCoefficients g x =ᶠ[𝓝 (c x)] metricCoefficients g' x := by
    filter_upwards [ht.eventually he] with y hy
    funext i j
    exact hy _ _
  have hf (i : CoordIndex E) : (fun y => metricFlux g u x y i) =ᶠ[𝓝 (c x)]
      (fun y => metricFlux g' u x y i) := by
    filter_upwards [hc] with y hy
    simp only [metricFlux,hy]
  change (Real.sqrt (metricCoefficients g x (c x)).det)⁻¹ *
    ∑ i, fderiv ℝ (fun y => metricFlux g u x y i) (c x) (Module.finBasis ℝ E i) = _
  rw [hc.self_of_nhds]
  simp_rw [(hf _).fderiv_eq]
  rfl
end MetricLocality

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_TransverseZeroKernel
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
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma laplaceBeltrami_add {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun y => u y + v y) x =
      laplaceBeltrami g u x + laplaceBeltrami g v x := by
  have h := congrArg Complex.re (complexLaplaceBeltrami_add
    (Complex.ofRealCLM.contMDiff.comp hu) (Complex.ofRealCLM.contMDiff.comp hv) g x)
  simpa only [complexLaplaceBeltrami, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
    Function.comp_def, Complex.ofRealCLM_apply, Pi.sub_apply] using h

end

open Set Filter Function Manifold
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
lemma three_metricCoefficients_first (p : ThreeManifold) (i j : CoordIndex ThreeModel) :
    HasFDerivAt (fun y => metricCoefficients threeBackgroundMetric p y i j)
      (0 : ThreeModel →L[ℝ] ℝ) 0 := by
  simp_rw [three_metricCoefficients]
  exact lpProductRoundChart_metric_first _ _ _ _ (sphereFrame_orthogonal p.1)
    (unitSphereFrame_orthogonal p.2) _ _
lemma three_metricFirstCoefficient_zero (p : ThreeManifold) (j : CoordIndex ThreeModel) :
    metricFirstCoefficient threeBackgroundMetric p j 0 = 0 := by
  have hn : (metricCoefficients threeBackgroundMetric p 0).det ≠ 0 :=
    (metricCoefficients_det_pos threeBackgroundMetric p (by rw [three_chart_target]; trivial)).ne'
  have hh := fun i => (zero_jet_density_inverse (metricCoefficients threeBackgroundMetric p)
    (three_metricCoefficients_first p) hn i j).fderiv
  simp only [metricFirstCoefficient,hh,_root_.zero_apply,Finset.sum_const_zero,mul_zero]
theorem three_laplace_at_center (u : ThreeManifold → ℝ)
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (p : ThreeManifold) :
    laplaceBeltrami threeBackgroundMetric u p = ∑ i, ∑ j,
      (Matrix.gram ℝ (Module.finBasis ℝ ThreeModel))⁻¹ i j *
      fderiv ℝ (fun y => fderiv ℝ (u ∘ (chartAt ThreeModel p).symm) y
        (Module.finBasis ℝ ThreeModel j)) 0 (Module.finBasis ℝ ThreeModel i) := by
  rw [laplaceBeltrami_inChart hu threeBackgroundMetric p p (mem_chart_source _ _),three_chart_center,
    localLaplacian_expansion hu threeBackgroundMetric p (by rw [three_chart_target]; trivial)]
  simp only [three_metricCoefficients_zero,three_metricFirstCoefficient_zero,
    zero_mul,Finset.sum_const_zero,add_zero]
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
local instance threeModelContinuousSMul'_r8fb367_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.threeAmbientNormedSpace'
local instance threeAmbientContinuousSMul'_r8fb367_1 : ContinuousSMul ℝ ThreeAmbient := inferInstance
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
lemma threePower_chart (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) :
    threePower a b k ∘ (chartAt ThreeModel p).symm =
      fun z => (productSphere_fstPower (n:=2) (m:=1) p.1 (planarLinear a b) k z*
        productSphere_sndPower (n:=2) (m:=1) p.2 (planarLinear (1:ℂ) Complex.I) k z).re := by
  have hh := congrArg (fun f : ThreeModel → ℂ => fun x => (f x).re)
    (threeComplexPower_chart a b k p)
  exact hh

theorem threePower_eigen (a b : Euclidean 3) (k : ℕ) (hk : 2 ≤ k)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (p : ThreeManifold) :
    -laplaceBeltrami threeBackgroundMetric (threePower a b k) p =
      productFrequency k*threePower a b k p := by
  have hc : inner ℝ (1:ℂ) 1 = 1 := by simp
  have hd : inner ℝ Complex.I Complex.I = 1 := by simp
  have hcd : inner ℝ (1:ℂ) Complex.I = 0 := by simp [Complex.inner]
  have ht := productSphere_power_trace (Module.finBasis ℝ ThreeModel) p.1 p.2 a b
    (1:ℂ) Complex.I k k hk hk ha hb hab hc hd hcd
  have hfull : ContDiff ℝ ∞ (fun z : ThreeModel =>
      productSphere_fstPower (n:=2) (m:=1) p.1 (planarLinear a b) k z*
      productSphere_sndPower (n:=2) (m:=1) p.2 (planarLinear (1:ℂ) Complex.I) k z) :=
    (productSphere_fstPower_smooth _ _ _).mul (productSphere_sndPower_smooth _ _ _)
  rw [three_laplace_at_center _ (threePower_smooth _ _ _),threePower_chart]
  simp_rw [second_real_part hfull]
  have hr := congrArg Complex.re ht
  simp only [complexGramTrace,Complex.re_sum,Complex.re_ofReal_mul] at hr
  rw [hr,complexIdentityPlanar]
  have hf : -((k:ℂ)*((k:ℂ)+(2:ℂ)-1)+(k:ℂ)*((k:ℂ)+(1:ℂ)-1)) =
      (-(productFrequency k):ℂ) := by
    unfold productFrequency
    push_cast
    ring
  norm_num only [Nat.cast_ofNat]
  rw [hf, mul_assoc]
  simp only [neg_mul,Complex.neg_re,neg_neg,Complex.re_ofReal_mul]
  rfl
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
local instance threeCoupledContinuousSMul_r8fb367_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma product_laplace_const_mul (g : SmoothMetric ThreeModel ThreeManifold)
    {u : ThreeManifold → ℝ} (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) 2 u)
    (c : ℝ) (x : ThreeManifold) :
    laplaceBeltrami g (fun y => c*u y) x=c*laplaceBeltrami g u x := by
  have h := complexLaplaceBeltrami_const_mul (Complex.ofRealCLM.contMDiff.comp hu) (c:ℂ) g x
  change complexLaplaceBeltrami g (fun y => (c:ℂ)*(u y:ℂ)) x=(c:ℂ)*complexLaplaceBeltrami g (fun y => (u y:ℂ)) x at h
  have he : (fun y => (c:ℂ)*(u y:ℂ))=fun y => ((c*u y:ℝ):ℂ) := by ext y; simp
  rw [he,complexLaplaceBeltrami_ofReal,complexLaplaceBeltrami_ofReal] at h
  exact_mod_cast h
lemma product_laplace_linear_eigen (g : SmoothMetric ThreeModel ThreeManifold)
    (u v : ThreeManifold → ℝ) (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) 2 v) (c Λ : ℝ) (p : ThreeManifold)
    (he₁ : -laplaceBeltrami g u p=Λ*u p) (he₂ : -laplaceBeltrami g v p=Λ*v p) :
    -laplaceBeltrami g (fun x => u x+c*v x) p=Λ*(u p+c*v p) := by
  have hcv : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) 2 (fun x => c*v x) := contMDiff_const.mul hv
  have hadd := laplaceBeltrami_add hu hcv g p
  have hmul := product_laplace_const_mul g hv c p
  calc
    _ = -(laplaceBeltrami g u p+laplaceBeltrami g (fun x => c*v x) p) := congrArg Neg.neg hadd
    _ = -(laplaceBeltrami g u p+c*laplaceBeltrami g v p) := congrArg (fun z : ℝ => -(laplaceBeltrami g u p+z)) hmul
    _ = _ := by linear_combination he₁+c*he₂
lemma threeCoupled_eigen (r : ℝ) (k : ℕ) (hk : 2 ≤ k) (p : ThreeManifold) :
    -laplaceBeltrami threeBackgroundMetric (threeCoupled r k) p=productFrequency k*threeCoupled r k p := by
  have ha : inner ℝ (productAxis 0) (productAxis 0)=1 := by simp
  have hb : inner ℝ (productAxis 1) (productAxis 1)=1 := by simp
  have hc : inner ℝ (productAxis 2) (productAxis 2)=1 := by simp
  have hab : inner ℝ (productAxis 0) (productAxis 1)=0 := by norm_num [productAxis_inner,Fin.ext_iff]
  have hac : inner ℝ (productAxis 0) (productAxis 2)=0 := by norm_num [productAxis_inner,Fin.ext_iff]
  have h₁ := threePower_eigen _ _ k hk ha hb hab p
  have h₂ := threePower_eigen _ _ k hk ha hc hac p
  have h2 : (2:WithTop ℕ∞) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
  rw [threeCoupled_eq]
  exact product_laplace_linear_eigen threeBackgroundMetric _ _
    ((threePower_smooth _ _ _).of_le h2) ((threePower_smooth _ _ _).of_le h2) (r^k) _ p h₁ h₂
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


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

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
attribute [local instance] OAI.YauCounterexamples.threeGlobalResidualNormedSpace
local instance threeGlobalResidualContinuousSMul_r8fb367_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma threeCoupled_residual_tsupport (g : SmoothMetric ThreeModel ThreeManifold)
    {F : Set ThreeManifold} (hF : IsClosed F)
    (hext : ∀ p ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) p,
      g.inner p v w=threeBackgroundMetric.inner p v w)
    (k : ℕ) (hk : 2 ≤ k) :
    tsupport (fun p => laplaceBeltrami g (threeCoupled threeCouplingRadius k) p+
      productFrequency k*threeCoupled threeCouplingRadius k p)⊆F := by
  apply closure_minimal _ hF
  intro p hp
  by_contra hnot
  have hagree : ∀ᶠ z in 𝓝 p, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) z,
      g.inner z v w=threeBackgroundMetric.inner z v w := by
    filter_upwards [hF.isOpen_compl.mem_nhds hnot] with z hz
    exact hext z hz
  have hl := laplaceBeltrami_metric_congr_nhds g threeBackgroundMetric
    (threeCoupled threeCouplingRadius k) hagree
  have he := threeCoupled_eigen threeCouplingRadius k hk p
  exact hp (by dsimp only; linarith)

theorem threeCoupled_global_residual_rapid_decay_oai
    (g : SmoothMetric ThreeModel ThreeManifold) {F : Set ThreeManifold} (hF : IsClosed F)
    (hext : ∀ p ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) p,
      g.inner p v w=threeBackgroundMetric.inner p v w)
    {φ : ThreeManifold → ℝ} (hφ : Continuous φ) {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ p∈F, threeGlobalLog p+δ ≤ φ p)
    (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (h P : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ k≥N, ∀ y∈K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j ((fun z => laplaceBeltrami g (threeCoupled threeCouplingRadius k) z+
        productFrequency k*threeCoupled threeCouplingRadius k z) ∘ (chartAt ThreeModel p).symm) y‖ ≤
          ((k:ℝ)^P)⁻¹*Real.exp (productWaveFrequency k*φ ((chartAt ThreeModel p).symm y)) := by
  let J := K ∩ (chartAt ThreeModel p).symm ⁻¹' F
  have hc := three_chart_symm_continuous p
  have hJ : IsCompact J := hK.inter_right (hF.preimage hc)
  obtain ⟨N,hN,hr⟩ := threeCoupled_dominated_residual_rapid_decay g hφ p hJ h P hδ
    (fun y hy => hgap _ hy.2)
  refine ⟨max N 2,le_max_right _ _,?_⟩
  intro k hk y hy j hj
  by_cases hyF : (chartAt ThreeModel p).symm y∈F
  · exact hr k ((le_max_left _ _).trans hk) y ⟨hy,hyF⟩ j hj
  · let R : ThreeManifold → ℝ := fun z => laplaceBeltrami g (threeCoupled threeCouplingRadius k) z+
      productFrequency k*threeCoupled threeCouplingRadius k z
    have hs : tsupport R⊆F := threeCoupled_residual_tsupport g hF hext k ((le_max_right _ _).trans hk)
    have hz : R ∘ (chartAt ThreeModel p).symm =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [(hc.tendsto y).eventually (hF.isOpen_compl.mem_nhds hyF)] with z hz
      by_contra hm
      exact hz (hs (subset_closure hm))
    have hj0 := (hz.iteratedFDeriv ℝ j).eq_of_nhds
    change ‖iteratedFDeriv ℝ j (R ∘ (chartAt ThreeModel p).symm) y‖ ≤ _
    rw [hj0]
    cases j with
    | zero => simp only [norm_iteratedFDeriv_zero,norm_zero]; positivity
    | succ j => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; positivity
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.threeCoupled_global_residual_rapid_decay_oai := @OAI.YauCounterexamples.threeCoupled_global_residual_rapid_decay_oai
