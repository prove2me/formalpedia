-- Prove2me | solution 1 for OAI.YauCounterexamples.roundPower_global_profile_residual_rapid_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:41:50.246127+00:00
-- url     : https://prove2.me/submissions/482279b2-9006-4c0a-8e65-be84039f19b4

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A005
import Definitions.Def_OAIQ070A007
import Theorems.Thm_OAI_YauCounterexamples_roundPower_strict_profile_residual_rapid_decay

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

lemma inverse_gram_trace (b : Basis ι ℝ E) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b i) (b j) = Fintype.card ι := by
  have hh := Matrix.nonsing_inv_mul (Matrix.gram ℝ b)
    (isUnit_iff_ne_zero.mpr (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos.ne')
  have ht := congrArg Matrix.trace hh
  simpa [Matrix.trace,Matrix.diag,Matrix.mul_apply,real_inner_comm] using ht


end

open Set Filter Function Module
open scoped Topology ContDiff InnerProductSpace Matrix

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

lemma roundLinearPower_second (ℓ : E →L[ℝ] ℂ) (n : ℕ) (p : E)
    (L : F →ₗᵢ[ℝ] E) (v w : F) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => (ℓ (roundChart p L z))^n) y w) 0 v =
      (n:ℂ) * ((n-1:ℕ):ℂ) * (ℓ p)^(n-2) * ℓ (L v) * ℓ (L w) -
        (n:ℂ) * (ℓ p)^(n-1) * ℓ p * (inner ℝ w v : ℂ) := by
  have ha := (ℓ.hasFDerivAt.comp (0:F) (roundChart_first p L)).pow (n-1)
  have hb := ℓ.hasFDerivAt.comp (0:F) (roundChart_second p L w)
  have hh := (ha.const_mul (n:ℂ)).mul hb
  have he : (fun y => fderiv ℝ (fun z => (ℓ (roundChart p L z))^n) y w) =
      (fun y => (n:ℂ) * (ℓ (roundChart p L y))^(n-1)) *
        (fun y => ℓ (fderiv ℝ (roundChart p L) y w)) := by
    funext y
    exact roundLinearPower_directional ℓ n p L y w
  simp only [Function.comp_def] at hh
  rw [he]
  convert! congrArg (fun D => D v) hh.fderiv using 1
  all_goals try with_reducible_and_instances rfl
  simp [roundChart_zero,(roundChart_first p L).fderiv,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,_root_.smul_apply,
    smul_eq_mul,show n-1-1=n-2 by omega]
  ring

lemma roundLinearPower_second_of_two_le (ℓ : E →L[ℝ] ℂ) (n : ℕ) (hn : 2 ≤ n) (p : E)
    (L : F →ₗᵢ[ℝ] E) (v w : F) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => (ℓ (roundChart p L z))^n) y w) 0 v =
      (n:ℂ) * ((n:ℂ)-1) * (ℓ p)^(n-2) * ℓ (L v) * ℓ (L w) -
        (n:ℂ) * (ℓ p)^n * (inner ℝ w v : ℂ) := by
  rw [roundLinearPower_second]
  have h1 : ((n-1:ℕ):ℂ) = (n:ℂ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have h2 : (ℓ p)^(n-1) * ℓ p = (ℓ p)^n := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [h1]
  rw [mul_assoc (n:ℂ) ((ℓ p)^(n-1)),h2]
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

lemma roundLinearPower_real_second (ℓ : E →L[ℝ] ℂ) (n : ℕ) (hn : 2 ≤ n) (p : E)
    (L : F →ₗᵢ[ℝ] E) (v w : F) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => ((ℓ (roundChart p L z))^n).re) y w) 0 v =
      ((n:ℂ) * ((n:ℂ)-1) * (ℓ p)^(n-2) * ℓ (L v) * ℓ (L w) -
        (n:ℂ) * (ℓ p)^n * (inner ℝ w v : ℂ)).re := by
  have hf : ContDiff ℝ ∞ (fun z => (ℓ (roundChart p L z))^n) :=
    (ℓ.contDiff.comp (roundChart_smooth p L)).pow n
  rw [second_real_part hf,roundLinearPower_second_of_two_le ℓ n hn]




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

lemma sphere_inverse_gram_contraction (p : Sphere n) (a b : Euclidean (n+1)) :
    ∑ i, ∑ j, (Matrix.gram ℝ (Module.finBasis ℝ (Euclidean n)))⁻¹ i j *
      inner ℝ (sphereFrame p (Module.finBasis ℝ (Euclidean n) j)) a *
      inner ℝ (sphereFrame p (Module.finBasis ℝ (Euclidean n) i)) b =
      inner ℝ a b - inner ℝ (p : Euclidean (n+1)) a * inner ℝ (p : Euclidean (n+1)) b := by
  simp_rw [sphereFrame_inner]
  rw [inverse_gram_contraction,sphereCoordinates_inner]

section Planar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma planarLinear_apply (a b x : E) :
    planarLinear a b x = (inner ℝ a x : ℂ) + Complex.I * (inner ℝ b x : ℂ) := by
  rfl
lemma planarLinear_apply_flip (a b x : E) :
    planarLinear a b x = (inner ℝ x a : ℂ) + Complex.I * (inner ℝ x b : ℂ) := by
  rw [planarLinear_apply,real_inner_comm a x,real_inner_comm b x]
end Planar

lemma complex_bilinear_expand (r a b c d : ℝ) :
    (r:ℂ) * ((a:ℂ)+Complex.I*b) * ((c:ℂ)+Complex.I*d) =
      ((r*a*c-r*b*d:ℝ):ℂ) + Complex.I * ((r*a*d+r*b*c:ℝ):ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]


theorem sphere_planar_contraction (p : Sphere n) (a b : Euclidean (n+1))
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    ∑ i, ∑ j, ((Matrix.gram ℝ (Module.finBasis ℝ (Euclidean n)))⁻¹ i j : ℂ) *
      planarLinear a b (sphereFrame p (Module.finBasis ℝ (Euclidean n) j)) *
      planarLinear a b (sphereFrame p (Module.finBasis ℝ (Euclidean n) i)) =
        -(planarLinear a b (p : Euclidean (n+1)))^2 := by
  simp_rw [planarLinear_apply_flip,complex_bilinear_expand]
  simp_rw [Finset.sum_add_distrib,← Finset.mul_sum,← Complex.ofReal_sum,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib]
  rw [sphere_inverse_gram_contraction,sphere_inverse_gram_contraction,
    sphere_inverse_gram_contraction,sphere_inverse_gram_contraction]
  rw [ha,hb,hab,real_inner_comm a b,hab]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,pow_two]; ring



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

variable {n : ℕ}

variable (g : SmoothMetric (Euclidean n) (Sphere n))
variable (hg : ∀ (p : Sphere n) (v w : TangentSpace 𝓘(ℝ,Euclidean n) p),
  g.inner p v w = (inner ℝ : Euclidean (n+1) → Euclidean (n+1) → ℝ)
    (mfderiv 𝓘(ℝ,Euclidean n) 𝓘(ℝ,Euclidean (n+1))
      (fun q : Sphere n => (q : Euclidean (n+1))) p v)
    (mfderiv 𝓘(ℝ,Euclidean n) 𝓘(ℝ,Euclidean (n+1))
      (fun q : Sphere n => (q : Euclidean (n+1))) p w))

include hg

lemma round_metricCoefficients (p : Sphere n) (y : Euclidean n) (i j : CoordIndex (Euclidean n)) :
    metricCoefficients g p y i j =
      inner ℝ (fderiv ℝ (roundChart (p : Euclidean (n+1)) (sphereFrame p)) y (Module.finBasis ℝ (Euclidean n) i))
        (fderiv ℝ (roundChart (p : Euclidean (n+1)) (sphereFrame p)) y (Module.finBasis ℝ (Euclidean n) j)) := by
  rw [metricCoefficients,hg]
  simp only [coordinateVector,sphere_coordinate_embedding]

lemma round_metricCoefficients_zero (p : Sphere n) :
    metricCoefficients g p 0 = Matrix.gram ℝ (Module.finBasis ℝ (Euclidean n)) := by
  ext i j
  rw [round_metricCoefficients g hg,(roundChart_first _ _).fderiv]
  exact (sphereFrame p).inner_map_map _ _

lemma round_metricCoefficients_first (p : Sphere n) (i j : CoordIndex (Euclidean n)) :
    HasFDerivAt (fun y => metricCoefficients g p y i j) (0 : Euclidean n →L[ℝ] ℝ) 0 := by
  simp_rw [round_metricCoefficients g hg]
  exact roundChart_metric_first _ _ (sphereFrame_orthogonal p) _ _

lemma round_metricFirstCoefficient_zero (p : Sphere n) (j : CoordIndex (Euclidean n)) :
    metricFirstCoefficient g p j 0 = 0 := by
  have hn : (metricCoefficients g p 0).det ≠ 0 :=
    (metricCoefficients_det_pos g p (by rw [sphere_chart_target]; trivial)).ne'
  have hh := fun i => (zero_jet_density_inverse (metricCoefficients g p)
    (round_metricCoefficients_first g hg p) hn i j).fderiv
  simp only [metricFirstCoefficient,hh,_root_.zero_apply,Finset.sum_const_zero,mul_zero]

theorem round_laplace_at_center (u : Sphere n → ℝ)
    (hu : ContMDiff 𝓘(ℝ,Euclidean n) 𝓘(ℝ,ℝ) ∞ u) (p : Sphere n) :
    laplaceBeltrami g u p = ∑ i, ∑ j,
      (Matrix.gram ℝ (Module.finBasis ℝ (Euclidean n)))⁻¹ i j *
      fderiv ℝ (fun y => fderiv ℝ (u ∘ (chartAt (Euclidean n) p).symm) y
        (Module.finBasis ℝ (Euclidean n) j)) 0 (Module.finBasis ℝ (Euclidean n) i) := by
  rw [laplaceBeltrami_inChart hu g p p (mem_chart_source _ _),sphere_chart_center,
    localLaplacian_expansion hu g p (by rw [sphere_chart_target]; trivial)]
  simp only [round_metricCoefficients_zero g hg,round_metricFirstCoefficient_zero g hg,
    zero_mul,Finset.sum_const_zero,add_zero]



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

lemma complex_inverse_gram_trace :
    ∑ i, ∑ j, ((Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)))⁻¹ i j : ℂ) *
      (inner ℝ (Module.finBasis ℝ (Euclidean d) j) (Module.finBasis ℝ (Euclidean d) i) : ℂ) = (d:ℂ) := by
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum,real_inner_comm
    (Module.finBasis ℝ (Euclidean d) _) (Module.finBasis ℝ (Euclidean d) _)]
  rw [inverse_gram_trace]
  simp [Euclidean]

lemma roundPower_complex_hessian_trace (a b : Euclidean (d+1)) (k : ℕ) (hk : 2 ≤ k)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) (p : Sphere d) :
    ∑ i, ∑ j, ((Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)))⁻¹ i j : ℂ) *
      ((k:ℂ) * ((k:ℂ)-1) * (planarLinear a b p)^(k-2) *
          planarLinear a b (sphereFrame p (Module.finBasis ℝ (Euclidean d) i)) *
          planarLinear a b (sphereFrame p (Module.finBasis ℝ (Euclidean d) j)) -
        (k:ℂ) * (planarLinear a b p)^k *
          (inner ℝ (Module.finBasis ℝ (Euclidean d) j) (Module.finBasis ℝ (Euclidean d) i) : ℂ)) =
      -(k:ℂ) * ((k:ℂ)+(d:ℂ)-1) * (planarLinear a b p)^k := by
  let z := planarLinear a b (p : Euclidean (d+1))
  calc
    _ = (k:ℂ) * ((k:ℂ)-1) * z^(k-2) *
        (∑ i, ∑ j, ((Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)))⁻¹ i j : ℂ) *
          planarLinear a b (sphereFrame p (Module.finBasis ℝ (Euclidean d) j)) *
          planarLinear a b (sphereFrame p (Module.finBasis ℝ (Euclidean d) i))) -
        (k:ℂ) * z^k * (∑ i, ∑ j,
          ((Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)))⁻¹ i j : ℂ) *
          (inner ℝ (Module.finBasis ℝ (Euclidean d) j) (Module.finBasis ℝ (Euclidean d) i) : ℂ)) := by
      simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [z]
      ring
    _ = -(k:ℂ) * ((k:ℂ)+(d:ℂ)-1) * z^k := by
      rw [sphere_planar_contraction p a b ha hb hab,complex_inverse_gram_trace]
      have hp : z^(k-2) * z^2 = z^k := by rw [← pow_add,Nat.sub_add_cancel hk]
      change (k:ℂ) * ((k:ℂ)-1) * z^(k-2) * -(z^2) - (k:ℂ) * z^k * (d:ℂ) = _
      rw [mul_neg, mul_assoc ((k:ℂ) * ((k:ℂ)-1)), hp]
      ring

variable (g : SmoothMetric (Euclidean d) (Sphere d))
variable (hg : ∀ (p : Sphere d) (v w : TangentSpace 𝓘(ℝ,Euclidean d) p),
  g.inner p v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
    (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
      (fun q : Sphere d => (q : Euclidean (d+1))) p v)
    (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
      (fun q : Sphere d => (q : Euclidean (d+1))) p w))

include hg

theorem roundPower_eigen (a b : Euclidean (d+1)) (k : ℕ) (hk : 2 ≤ k)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) (p : Sphere d) :
    -laplaceBeltrami g (roundPower a b k) p =
      (k:ℝ) * ((k:ℝ)+(d:ℝ)-1) * roundPower a b k p := by
  rw [round_laplace_at_center g hg _ (roundPower_smooth a b k)]
  have hc : roundPower a b k ∘ (chartAt (Euclidean d) p).symm =
      fun z => ((planarLinear a b (roundChart (p : Euclidean (d+1)) (sphereFrame p) z))^k).re := by
    funext z
    simp only [roundPower,Function.comp_apply]
    rw [← sphere_chart_symm]
  simp_rw [hc,roundLinearPower_real_second _ k hk]
  have ht := congrArg Complex.re (roundPower_complex_hessian_trace a b k hk ha hb hab p)
  simp only [Complex.re_sum,Complex.re_ofReal_mul] at ht
  rw [ht]
  have hcast : -(k:ℂ) * ((k:ℂ)+(d:ℂ)-1) =
      ((-(k:ℝ) * ((k:ℝ)+(d:ℝ)-1) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast,Complex.re_ofReal_mul]
  dsimp [roundPower]
  ring


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

variable {d : ℕ}

theorem roundPower_residual_tsupport
    (g g₀ : SmoothMetric (Euclidean d) (Sphere d))
    (hg₀ : ∀ (p : Sphere d) (v w : TangentSpace 𝓘(ℝ,Euclidean d) p),
      g₀.inner p v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
          (fun q : Sphere d => (q : Euclidean (d+1))) p v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
          (fun q : Sphere d => (q : Euclidean (d+1))) p w))
    {K : Set (Sphere d)} (hK : IsClosed K)
    (hext : ∀ p ∉ K, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean d) p, g.inner p v w = g₀.inner p v w)
    (a b : Euclidean (d+1)) (n : ℕ) (hn : 2 ≤ n)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    tsupport (fun z => laplaceBeltrami g (roundPower a b n) z +
      (n:ℝ)*((n:ℝ)+(d:ℝ)-1)*roundPower a b n z) ⊆ K := by
  apply closure_minimal _ hK
  intro z hz
  by_contra hzK
  have hagree : ∀ᶠ p in 𝓝 z, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean d) p,
      g.inner p v w = g₀.inner p v w := by
    filter_upwards [hK.isOpen_compl.mem_nhds hzK] with p hp
    exact hext p hp
  have hl := laplaceBeltrami_metric_congr_nhds g g₀ (roundPower a b n) hagree
  have hr := roundPower_eigen g₀ hg₀ a b n hn ha hb hab z
  exact hz (by dsimp only; linarith)

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RoundPowerGlobalProfileResidual
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

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

theorem roundPower_global_profile_residual_rapid_decay_oai
    (g g₀ : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg₀ : ∀ (x : Sphere 3) (v w : TangentSpace 𝓘(ℝ,Euclidean 3) x),
      g₀.inner x v w = (inner ℝ : Euclidean 4 → Euclidean 4 → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4)
          (fun q : Sphere 3 => (q : Euclidean 4)) x v)
        (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4)
          (fun q : Sphere 3 => (q : Euclidean 4)) x w))
    {F : Set (Sphere 3)} (hF : IsClosed F)
    (hext : ∀ x ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) x,
      g.inner x v w = g₀.inner x v w)
    (a b : Euclidean 4) (ha : inner ℝ a a=1) (hb : inner ℝ b b=1)
    (hab : inner ℝ a b=0) (p : Sphere 3) {K : Set (Euclidean 3)}
    (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean 3) p).target)
    (φ : Euclidean 3 → ℝ) (hφ : ContinuousOn φ K) (h P : ℕ)
    (hgap : ∀ y ∈ K, (chartAt (Euclidean 3) p).symm y ∈ F →
      roundPlanarChart a b p y ≠ 0 → Real.log ‖roundPlanarChart a b p y‖ < φ y) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j
        ((fun z => laplaceBeltrami g (roundPower a b n) z +
          (n:ℝ)*((n:ℝ)+2)*roundPower a b n z) ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤
        ((n:ℝ)^P)⁻¹*Real.exp ((n:ℝ)*φ y) := by
  have hc : Continuous (chartAt (Euclidean 3) p).symm := by
    have hh := (chartAt (Euclidean 3) p).continuousOn_symm
    rwa [sphere_chart_target, continuousOn_univ] at hh
  let J := K ∩ (chartAt (Euclidean 3) p).symm ⁻¹' F
  have hJ : IsCompact J := hK.inter_right (hF.preimage hc)
  obtain ⟨N,hN,hr⟩ := roundPower_strict_profile_residual_rapid_decay g a b p hJ
    (fun y hy => hKO hy.1) φ (hφ.mono inter_subset_left) h P
    (fun y hy => hgap y hy.1 hy.2)
  refine ⟨max N 2,le_max_right _ _,?_⟩
  intro n hn y hy j hj
  by_cases hyF : (chartAt (Euclidean 3) p).symm y ∈ F
  · exact hr n ((le_max_left _ _).trans hn) y ⟨hy,hyF⟩ j hj
  · have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
    let R : Sphere 3 → ℝ := fun z => laplaceBeltrami g (roundPower a b n) z +
      (n:ℝ)*((n:ℝ)+2)*roundPower a b n z
    have hs : tsupport R ⊆ F := by
      have hs' := roundPower_residual_tsupport g g₀ hg₀ hF hext a b n hn2 ha hb hab
      have hh : (n:ℝ)+3-1 = (n:ℝ)+2 := by ring
      simpa only [Nat.cast_ofNat,hh] using hs'
    have hz : R ∘ (chartAt (Euclidean 3) p).symm =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [(hc.tendsto y).eventually (hF.isOpen_compl.mem_nhds hyF)] with z hz
      by_contra hm
      exact hz (hs (subset_closure hm))
    have hj0 := (hz.iteratedFDeriv ℝ j).eq_of_nhds
    change ‖iteratedFDeriv ℝ j (R ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤ _
    rw [hj0]
    cases j with
    | zero => simp only [norm_iteratedFDeriv_zero,norm_zero]; positivity
    | succ j => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; positivity


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.roundPower_global_profile_residual_rapid_decay_oai := @OAI.YauCounterexamples.roundPower_global_profile_residual_rapid_decay_oai
