-- Prove2me | solution 1 for OAI.YauCounterexamples.annular_eigenfunction_separating_tensor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:22:46.104532+00:00
-- url     : https://prove2.me/submissions/95a39eed-80cc-4e97-9e84-a3dc196d09e0

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007
import Definitions.Def_OAIQ070A008
import Theorems.Thm_OAI_YauCounterexamples_annular_orthogonal_transverse_nonzero
import Theorems.Thm_OAI_YauCounterexamples_exists_supported_separating_tensor

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
end Planar



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_AnnularRelativeMargin
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
open scoped Topology ContDiff InnerProductSpace Matrix
variable {d : ℕ}

lemma ambientPowerGradient_pair (a b : Euclidean (d+1)) (k : ℕ) (x v : Euclidean (d+1)) :
    inner ℝ v (ambientPowerGradient a b k x) =
      ((k:ℂ) * (planarLinear a b x)^(k-1) * planarLinear a b v).re := by
  simp only [ambientPowerGradient,inner_smul_right,inner_sub_right,
    planarLinear_apply,Complex.mul_re,Complex.mul_im,Complex.natCast_re,
    Complex.natCast_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,
    zero_add,add_zero,one_mul]
  rw [real_inner_comm a v,real_inner_comm b v]
  ring

lemma roundPower_chart_directional (a b : Euclidean (d+1)) (k : ℕ) (p : Sphere d) (v : Euclidean d) :
    fderiv ℝ (roundPower a b k ∘ (chartAt (Euclidean d) p).symm) 0 v =
      inner ℝ (sphereFrame p v) (ambientPowerGradient a b k p) := by
  have hc : roundPower a b k ∘ (chartAt (Euclidean d) p).symm =
      fun z => ((planarLinear a b (roundChart (p : Euclidean (d+1)) (sphereFrame p) z))^k).re := by
    funext z
    simp only [roundPower,Function.comp_apply]
    rw [← sphere_chart_symm]
  have hf : ContDiff ℝ ∞ (fun z => (planarLinear a b (roundChart (p : Euclidean (d+1)) (sphereFrame p) z))^k) :=
    ((planarLinear a b).contDiff.comp (roundChart_smooth _ _)).pow k
  rw [hc,fderiv_real_part (hf.differentiable (by simp) _),roundLinearPower_directional,
    roundChart_zero,(roundChart_first _ _).fderiv,ambientPowerGradient_pair]
  rfl

lemma ambientPowerGradient_norm_sq (a b : Euclidean (d+1)) (k : ℕ) (x : Euclidean (d+1))
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    inner ℝ (ambientPowerGradient a b k x) (ambientPowerGradient a b k x) =
      (k:ℝ)^2 * (Complex.normSq (planarLinear a b x))^(k-1) := by
  have hba : inner ℝ b a = 0 := (real_inner_comm a b).trans hab
  simp only [ambientPowerGradient,inner_smul_left,inner_smul_right,inner_sub_left,
    inner_sub_right,ha,hb,hab,hba,conj_trivial,mul_one,mul_zero,sub_zero,zero_sub]
  rw [← map_pow Complex.normSq]
  simp only [Complex.normSq_apply]
  ring

lemma ambientPowerGradient_radial (a b : Euclidean (d+1)) (k : ℕ) (hk : 1 ≤ k) (x : Euclidean (d+1)) :
    inner ℝ x (ambientPowerGradient a b k x) = (k:ℝ) * ((planarLinear a b x)^k).re := by
  rw [ambientPowerGradient_pair,mul_assoc,← pow_succ,Nat.sub_add_cancel hk]
  simp [Complex.mul_re]

theorem roundPower_gradient_square (a b : Euclidean (d+1)) (k : ℕ) (hk : 1 ≤ k)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) (p : Sphere d) :
    ∑ i, ∑ j, (Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)))⁻¹ i j *
      fderiv ℝ (roundPower a b k ∘ (chartAt (Euclidean d) p).symm) 0 (Module.finBasis ℝ (Euclidean d) j) *
      fderiv ℝ (roundPower a b k ∘ (chartAt (Euclidean d) p).symm) 0 (Module.finBasis ℝ (Euclidean d) i) =
      (k:ℝ)^2 * ((Complex.normSq (planarLinear a b p))^(k-1) - (roundPower a b k p)^2) := by
  simp_rw [roundPower_chart_directional]
  rw [sphere_inverse_gram_contraction,ambientPowerGradient_norm_sq _ _ _ _ ha hb hab,
    ambientPowerGradient_radial _ _ _ hk]
  dsimp [roundPower]
  ring

lemma complex_power_real_sq_bound (z : ℂ) (k : ℕ) :
    (z^k).re^2 ≤ (Complex.normSq z)^k := by
  rw [← map_pow Complex.normSq,Complex.normSq_apply]
  nlinarith [sq_nonneg (z^k).im]

theorem roundPower_annulus_noncritical (a b : Euclidean (d+1)) (k : ℕ) (hk : 1 ≤ k)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) (p : Sphere d)
    (hpos : 0 < Complex.normSq (planarLinear a b p)) (hlt : Complex.normSq (planarLinear a b p) < 1) :
    fderiv ℝ (roundPower a b k ∘ (chartAt (Euclidean d) p).symm) 0 ≠ 0 := by
  have hlow : 0 < (Complex.normSq (planarLinear a b p))^(k-1) - (roundPower a b k p)^2 := by
    have hbnd := complex_power_real_sq_bound (planarLinear a b p) k
    have he : (Complex.normSq (planarLinear a b p))^k =
        (Complex.normSq (planarLinear a b p))^(k-1) * Complex.normSq (planarLinear a b p) := by
      rw [← pow_succ,Nat.sub_add_cancel hk]
    rw [he] at hbnd
    have hh := mul_pos (pow_pos hpos (k-1)) (sub_pos.mpr hlt)
    dsimp [roundPower]
    nlinarith
  have hh := roundPower_gradient_square a b k hk ha hb hab p
  intro hz
  simp only [hz,_root_.zero_apply,mul_zero,Finset.sum_const_zero] at hh
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp := mul_pos (sq_pos_of_pos hkpos) hlow
  linarith


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

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateGradientPairCongrNhds
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
variable {d : ℕ}
lemma sphere_chart_symm_continuous_general (p : Sphere d) : Continuous (chartAt (Euclidean d) p).symm := by
  rw [←continuousOn_univ]
  simpa only [sphere_chart_target] using (chartAt (Euclidean d) p).continuousOn_symm
lemma round_annulus_open (a b : Euclidean (d+1)) (l h : ℝ) :
    IsOpen {p : Sphere d | l < Complex.normSq (planarLinear a b p) ∧
      Complex.normSq (planarLinear a b p) < h} := by
  have hc : Continuous (fun p : Sphere d => Complex.normSq (planarLinear a b p)) :=
    Complex.continuous_normSq.comp ((planarLinear a b).continuous.comp continuous_subtype_val)
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)


end

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_AnnularOrthogonalTransverseNonzero
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace
section Gradient
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma metricGradient_ne_zero_of_chart (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target)
    (hd : fderiv ℝ (u ∘ (chartAt E p).symm) y ≠ 0) :
    metricGradient g u ((chartAt E p).symm y) ≠ 0 := by
  intro hz
  apply hd
  have hf := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) p) hy).mdifferentiableAt (by simp)
  have hh := mfderiv_comp y (hu.mdifferentiable (by simp)).mdifferentiableAt hf
  rw [mfderiv_eq_fderiv] at hh
  ext w
  have he : fderiv ℝ (u ∘ (chartAt E p).symm) y w =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u ((chartAt E p).symm y)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y w) :=
    congrArg (fun L => L w) hh
  rw [he,←metricGradient_pairing g u _ _,hz]
  simp
end Gradient
variable {d : ℕ}
lemma annular_gradient_ne_zero (g : SmoothMetric (Euclidean d) (Sphere d))
    (a b : Euclidean (d+1)) (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1)
    (hab : inner ℝ a b = 0) (n : ℕ) (hn : 1 ≤ n) {l h : ℝ}
    (hl : 0 < l) (hh : h < 1) {u : Sphere d → ℝ}
    (hu : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ u)
    (hup : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h → u p = roundPower a b n p)
    (p : Sphere d) (hpl : l < Complex.normSq (planarLinear a b p))
    (hph : Complex.normSq (planarLinear a b p) < h) : metricGradient g u p ≠ 0 := by
  have hp : (chartAt (Euclidean d) p).symm 0 = p := by
    simpa only [sphere_chart_center] using (chartAt (Euclidean d) p).left_inv (mem_chart_source _ p)
  have hA := round_annulus_open a b l h
  have he : (u ∘ (chartAt (Euclidean d) p).symm) =ᶠ[𝓝 0]
      (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) := by
    have hx : (0 : Euclidean d) ∈ (chartAt (Euclidean d) p).symm ⁻¹'
        {q : Sphere d | l < Complex.normSq (planarLinear a b q) ∧
          Complex.normSq (planarLinear a b q) < h} := by
      change l < Complex.normSq (planarLinear a b ((chartAt (Euclidean d) p).symm 0)) ∧ _
      rw [hp]; exact ⟨hpl,hph⟩
    filter_upwards [(hA.preimage (sphere_chart_symm_continuous_general p)).mem_nhds hx] with y hy
    exact hup _ hy.1 hy.2
  have hd : fderiv ℝ (u ∘ (chartAt (Euclidean d) p).symm) 0 ≠ 0 := by
    rw [he.fderiv_eq]
    exact roundPower_annulus_noncritical a b n hn ha hb hab p (hl.trans hpl) (hph.trans hh)
  have hz := metricGradient_ne_zero_of_chart g hu p
    (show (0 : Euclidean d) ∈ (chartAt (Euclidean d) p).target by
      rw [sphere_chart_target]; exact mem_univ _) hd
  change (fun q : Sphere d => metricGradient g u q ≠ 0) ((chartAt (Euclidean d) p).symm 0) at hz
  rw [hp] at hz
  exact hz

end

open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}

theorem annular_eigenfunction_separating_tensor_oai [PreconnectedSpace (Sphere d)]
    (μ : Measure (Sphere d)) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (g : SmoothMetric (Euclidean d) (Sphere d))
    (a b c : Euclidean (d+1))
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hc : inner ℝ c c = 1)
    (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (n : ℕ) (hn : 2 ≤ n) {l h : ℝ} (hl : 0 < l) (hlh : l < h) (hh : h < 1)
    {u v : Sphere d → ℝ}
    (hu : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ v)
    (hue : ∀ p, -laplaceBeltrami g u p = ((n:ℝ)*((n:ℝ)+2))*u p)
    (hve : ∀ p, -laplaceBeltrami g v p = ((n:ℝ)*((n:ℝ)+2))*v p)
    (hup : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h → u p = roundPower a b n p)
    (hgp : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h →
      ∀ (X Y : TangentSpace 𝓘(ℝ,Euclidean d) p),
        g.inner p X Y = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
          (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
            (fun q : Sphere d => (q : Euclidean (d+1))) p X)
          (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
            (fun q : Sphere d => (q : Euclidean (d+1))) p Y))
    (hv0 : v ≠ 0) (ho : ∫ q, v q*u q ∂μ = 0) (hd : d = 3) :
    ∃ χ : Sphere d → ℝ,
      tsupport χ ⊆ {p | l < Complex.normSq (planarLinear a b p) ∧
        Complex.normSq (planarLinear a b p) < h} ∧
      ContMDiff 𝓘(ℝ,Euclidean d)
        (𝓘(ℝ,Euclidean d).prod 𝓘(ℝ,Euclidean d →L[ℝ] Euclidean d)) ∞
        (fun y => TotalSpace.mk' (Euclidean d →L[ℝ] Euclidean d) y
          (supportedPinningTensor g u v χ y)) ∧
      (∀ y, LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,Euclidean d) y)
        (supportedPinningTensor g u v χ y).toLinearMap = 0) ∧
      (∀ y, supportedPinningTensor g u v χ y (metricGradient g u y) = 0) ∧
      0 < ∫ y, g.inner y (metricGradient g v y)
        (supportedPinningTensor g u v χ y (metricGradient g v y)) ∂μ := by
  obtain ⟨p,hpl,hph,hp⟩ := annular_orthogonal_transverse_nonzero μ g a b c ha hb hc hab hac hbc
    n hn hl hlh hh hu hv hue hve hup hgp hv0 ho
  exact exists_supported_separating_tensor μ g hu hv (round_annulus_open a b l h)
    (fun q hq => annular_gradient_ne_zero g a b ha hb hab n (by omega) hl hh hu hup q hq.1 hq.2)
    ⟨hpl,hph⟩ hp (by simpa [Euclidean] using hd)




end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.annular_eigenfunction_separating_tensor_oai := @OAI.YauCounterexamples.annular_eigenfunction_separating_tensor_oai
