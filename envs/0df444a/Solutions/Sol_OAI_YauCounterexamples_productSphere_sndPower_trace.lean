-- Prove2me | solution 1 for OAI.YauCounterexamples.productSphere_sndPower_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:18:41.313535+00:00
-- url     : https://prove2.me/submissions/e3073906-21b3-48ea-a279-b95f31e977af

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A003
import Definitions.Def_OAIQ070A004

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
lemma second_linear_comp (L : E →L[ℝ] F) {f : F → ℂ}
    (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (f ∘ L) y w) x v =
      fderiv ℝ (fun y => fderiv ℝ f y (L w)) (L x) (L v) := by
  simp_rw [directional_linear_comp L (hf.differentiable (by simp))]
  exact directional_linear_comp L
    (((hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)) x v
end YauCounterexamples
end

end OAI
end

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


end

open Set Filter Function Module
open scoped Topology ContDiff InnerProductSpace Matrix
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma lp_inverse_gram_snd_contraction (b : Basis ι ℝ (WithLp 2 (E×F))) (u v : F) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b j).snd u * inner ℝ (b i).snd v = inner ℝ u v := by
  have h := inverse_gram_contraction b (WithLp.toLp 2 ((0:E),u)) (WithLp.toLp 2 ((0:E),v))
  simpa [WithLp.prod_inner_apply] using h
lemma lp_inverse_gram_snd_trace [FiniteDimensional ℝ F] (b : Basis ι ℝ (WithLp 2 (E×F))) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * inner ℝ (b j).snd (b i).snd = Module.finrank ℝ F := by
  let e := stdOrthonormalBasis ℝ F
  have h (x y : F) : inner ℝ x y = ∑ k, inner ℝ x (e k)*inner ℝ y (e k) := by
    rw [← e.sum_inner_mul_inner x y]
    apply Finset.sum_congr rfl
    intro k _
    rw [real_inner_comm (e k) y]
  have h₁ (i j : ι) : inner ℝ (b j).snd (b i).snd =
      ∑ k, inner ℝ (b j).snd (e k)*inner ℝ (b i).snd (e k) := h _ _
  simp_rw [h₁,Finset.mul_sum]
  have hs : (∑ i, ∑ j, ∑ k, (Matrix.gram ℝ b)⁻¹ i j *
      (inner ℝ (b j).snd (e k)*inner ℝ (b i).snd (e k))) =
      ∑ k, ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j *
        (inner ℝ (b j).snd (e k)*inner ℝ (b i).snd (e k)) := by
    calc
      _ = ∑ i, ∑ k, ∑ j, (Matrix.gram ℝ b)⁻¹ i j *
          (inner ℝ (b j).snd (e k)*inner ℝ (b i).snd (e k)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hs]
  simp_rw [← mul_assoc,lp_inverse_gram_snd_contraction]
  simp [e.orthonormal.1]

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




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

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
lemma planarLinear_apply_flip (a b x : E) :
    planarLinear a b x = (inner ℝ x a : ℂ) + Complex.I * (inner ℝ x b : ℂ) := by
  rw [planarLinear_apply,real_inner_comm a x,real_inner_comm b x]
end Planar

lemma complex_bilinear_expand (r a b c d : ℝ) :
    (r:ℂ) * ((a:ℂ)+Complex.I*b) * ((c:ℂ)+Complex.I*d) =
      ((r*a*c-r*b*d:ℝ):ℂ) + Complex.I * ((r*a*d+r*b*c:ℝ):ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]



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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ProductSphereFstContraction
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
section ProductSphereContraction
variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
  {n m : ℕ} [Fact (Module.finrank ℝ A = n+1)] [Fact (Module.finrank ℝ B = m+1)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [FiniteDimensional ℝ B] in
lemma productSphere_snd_contraction (b : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (q : Metric.sphere (0:B) 1) (a c : B) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j *
      inner ℝ (unitSphereFrame q (b j).snd) a * inner ℝ (unitSphereFrame q (b i).snd) c =
        inner ℝ a c-inner ℝ (q:B) a*inner ℝ (q:B) c := by
  simp_rw [unitSphereFrame_inner]
  rw [lp_inverse_gram_snd_contraction,unitSphereCoordinates_inner]
omit [FiniteDimensional ℝ B] in
lemma productSphere_snd_planar_contraction
    (e : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (p : Metric.sphere (0:B) 1) (a b : B)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    ∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j : ℂ) *
      planarLinear a b (unitSphereFrame p (e j).snd) *
      planarLinear a b (unitSphereFrame p (e i).snd) = -(planarLinear a b (p : B))^2 := by
  simp_rw [planarLinear_apply_flip,complex_bilinear_expand]
  simp_rw [Finset.sum_add_distrib,← Finset.mul_sum,← Complex.ofReal_sum,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib]
  rw [productSphere_snd_contraction,productSphere_snd_contraction,
    productSphere_snd_contraction,productSphere_snd_contraction]
  rw [ha,hb,hab,real_inner_comm a b,hab]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,pow_two]; ring
end ProductSphereContraction
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

omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_second (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ)
    (k : ℕ) (hk : 2 ≤ k) (v w : WithLp 2 (Euclidean n×Euclidean m)) :
    fderiv ℝ (fun y => fderiv ℝ (productSphere_sndPower p ℓ k) y w) 0 v =
      (k:ℂ)*((k:ℂ)-1)*(ℓ p)^(k-2)*ℓ (unitSphereFrame (n:=m) p v.snd)*
        ℓ (unitSphereFrame (n:=m) p w.snd) -
      (k:ℂ)*(ℓ p)^k*(inner ℝ w.snd v.snd:ℂ) := by
  unfold productSphere_sndPower
  have hf : ContDiff ℝ ∞ (fun y : Euclidean m => (ℓ (roundChart (p:B) (unitSphereFrame (n:=m) p) y))^k) := (ℓ.contDiff.comp (roundChart_smooth _ _)).pow k
  rw [second_linear_comp (WithLp.sndL 2 ℝ (Euclidean n) (Euclidean m)) (f:=(fun y : Euclidean m => (ℓ (roundChart (p:B) (unitSphereFrame (n:=m) p) y))^k)) hf]
  simp only [ContinuousLinearMap.map_zero]
  exact roundLinearPower_second_of_two_le ℓ k hk _ _ _ _
omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_trace_oai (e : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (p : Metric.sphere (0:B) 1) (a b : B) (k : ℕ) (hk : 2 ≤ k)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    complexGramTrace e (fun v w => fderiv ℝ
      (fun y => fderiv ℝ (productSphere_sndPower p (planarLinear a b) k) y w) 0 v) =
      -(k:ℂ)*((k:ℂ)+(m:ℂ)-1)*(planarLinear a b p)^k := by
  simp_rw [productSphere_sndPower_second p _ k hk]
  have ht : (∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j:ℂ)*
      (inner ℝ (e j).snd (e i).snd:ℂ)) = (m:ℂ) := by
    simp only [← Complex.ofReal_mul,← Complex.ofReal_sum]
    rw [lp_inverse_gram_snd_trace]
    simp [Euclidean]
  let z := planarLinear a b (p:B)
  calc
    _ = (k:ℂ)*((k:ℂ)-1)*z^(k-2)*
        (∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j:ℂ)*
          planarLinear a b (unitSphereFrame p (e j).snd)*
          planarLinear a b (unitSphereFrame p (e i).snd)) -
        (k:ℂ)*z^k*(∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j:ℂ)*
          (inner ℝ (e j).snd (e i).snd:ℂ)) := by
      unfold complexGramTrace
      simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [z]
      ring
    _ = _ := by
      rw [productSphere_snd_planar_contraction e p a b ha hb hab,ht]
      have hp : z^(k-2)*z^2=z^k := by rw [← pow_add,Nat.sub_add_cancel hk]
      change (k:ℂ)*((k:ℂ)-1)*z^(k-2)* -(z^2)-(k:ℂ)*z^k*(m:ℂ) = _
      rw [mul_neg,mul_assoc ((k:ℂ)*((k:ℂ)-1)),hp]
      dsimp [z]
      ring
end YauCounterexamples
end

end OAI
end

theorem solution.{u_2, u_3} : type_of% @OAI.YauCounterexamples.productSphere_sndPower_trace_oai.{u_2, u_3} := @OAI.YauCounterexamples.productSphere_sndPower_trace_oai.{u_2, u_3}
