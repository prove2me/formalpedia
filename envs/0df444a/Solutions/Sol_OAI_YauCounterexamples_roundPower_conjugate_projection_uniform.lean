-- Prove2me | solution 1 for OAI.YauCounterexamples.roundPower_conjugate_projection_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:40:40.556986+00:00
-- url     : https://prove2.me/submissions/14f00de2-37c0-4158-bdb7-701cc66b79be

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

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
end Planar



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LocalIntegrationParts
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
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

lemma roundPlanarChart_smooth (a b : Euclidean (d+1)) (p : Sphere d) :
    ContDiffOn ℝ ∞ (roundPlanarChart a b p) (chartAt (Euclidean d) p).target := by
  have hs : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℂ) ∞
      (fun q : Sphere d => planarLinear a b (q : Euclidean (d+1))) :=
    (planarLinear a b).contDiff.contMDiff.comp contMDiff_coe_sphere
  intro y hy
  exact (contMDiffAt_iff_contDiffAt.mp (hs.contMDiffAt.comp y
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy))).contDiffWithinAt

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ReciprocalIteratedDerivativeBound
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
namespace YauCounterexamples

lemma reciprocal_iterated_derivative_bound (j : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => 1/y) (Ioi 0) t‖ ≤ (j.factorial : ℝ) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_one_div j isOpen_Ioi ht0]
  have he : (-1-(j:ℤ)) = -((j+1 : ℕ):ℤ) := by omega
  dsimp only
  rw [he,zpow_neg,zpow_natCast]
  simp only [norm_mul,norm_pow,Real.norm_eq_abs,abs_neg,abs_one,one_pow,
    Nat.abs_cast,one_mul,norm_inv]
  have hp : 1 ≤ t^(j+1) := one_le_pow₀ ht
  have hi : |(t^(j+1))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg ht0.le _))]
    exact inv_le_one_of_one_le₀ hp
  simpa only [mul_one,abs_inv,abs_pow] using mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg j.factorial)

theorem normalized_reciprocal_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {x : E} (hx : 1 ≤ f x)
    (h : ℕ) (D : ℝ)
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j f x‖ ≤ D^j) :
    ‖iteratedFDeriv ℝ h (fun y => 1/f y) x‖ ≤ (h.factorial : ℝ)^2*D^h := by
  let S := {y | 0 < f y}
  have hS : IsOpen S := isOpen_lt continuous_const hf.continuous
  have hxS : x ∈ S := zero_lt_one.trans_le hx
  have hg : ContDiffOn ℝ ∞ (fun y : ℝ => 1/y) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun y hy => hy.ne')
  have hb := norm_iteratedFDerivWithin_comp_le hg hf.contDiffOn (show (h:ℕ∞ω) ≤ (∞ : ℕ∞ω) from le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    isOpen_Ioi.uniqueDiffOn hS.uniqueDiffOn (fun y (hy : y ∈ S) => hy) hxS
    (C:=(h.factorial:ℝ)) (D:=D) (fun j hj =>
      (reciprocal_iterated_derivative_bound j hx).trans (by exact_mod_cast Nat.factorial_le hj))
    (fun j hj hjh => by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hS.uniqueDiffOn (hf.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt hxS]
      exact hD j hj hjh)
  change ‖iteratedFDerivWithin ℝ h (fun y => 1/f y) S x‖ ≤ _ at hb
  have hrec : ContDiffAt ℝ h (fun y => 1/f y) x :=
    (contDiffAt_const.div hf.contDiffAt (zero_lt_one.trans_le hx).ne').of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hS.uniqueDiffOn hrec hxS] at hb
  simpa only [Function.comp_apply,pow_two,mul_assoc] using hb

theorem weighted_reciprocal_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {x : E} (h : ℕ)
    {δ W M R : ℝ} (hδ : 0 < δ) (hW : 0 < W) (hR : 0 ≤ R) (hx : δ*W^2 ≤ f x)
    (hjet : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j f x‖ ≤ M*R^j*W^2) :
    ‖iteratedFDeriv ℝ h (fun y => 1/f y) x‖ ≤
      (h.factorial : ℝ)^2 * (max 1 (M/δ)*R)^h / (δ*W^2) := by
  let c := δ*W^2
  have hc : 0 < c := mul_pos hδ (sq_pos_of_pos hW)
  let F : E → ℝ := fun y => c⁻¹*f y
  have hF : ContDiff ℝ ∞ F := contDiff_const.mul hf
  have hxF : 1 ≤ F x := by
    dsimp only [F]
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hc).mpr (by simpa only [one_mul] using hx)
  have hD : ∀ j : ℕ, 1 ≤ j → j ≤ h →
      ‖iteratedFDeriv ℝ j F x‖ ≤ (max 1 (M/δ)*R)^j := by
    intro j hj hjh
    have hej : iteratedFDeriv ℝ j F x = c⁻¹ • iteratedFDeriv ℝ j f x := by
      simpa only [F,smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply' (a:=c⁻¹) (x:=x) (hf.of_le
          (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt)
    rw [hej,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hc)]
    calc
      c⁻¹*‖iteratedFDeriv ℝ j f x‖ ≤ c⁻¹*(M*R^j*W^2) :=
        mul_le_mul_of_nonneg_left (hjet j hj hjh) (inv_nonneg.mpr hc.le)
      _ = (M/δ)*R^j := by dsimp only [c]; field_simp
      _ ≤ (max 1 (M/δ))^j*R^j := mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_self_pow₀ (le_max_left _ _) (by omega))) (pow_nonneg hR j)
      _ = (max 1 (M/δ)*R)^j := (mul_pow _ _ _).symm
  have hb := normalized_reciprocal_jet_bound hF hxF h (max 1 (M/δ)*R) hD
  have hfx : f x ≠ 0 := (hc.trans_le hx).ne'
  have hrec : ContDiffAt ℝ h (fun y => 1/f y) x :=
    (contDiffAt_const.div hf.contDiffAt hfx).of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
  have he : (fun y => 1/F y) = fun y => c • (1/f y) := by
    funext y
    simp only [F,one_div,smul_eq_mul,mul_inv_rev,inv_inv]
    ring
  rw [he,iteratedFDeriv_const_smul_apply' hrec,norm_smul,
    Real.norm_eq_abs,abs_of_pos hc] at hb
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb)

lemma geometric_product_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (h : ℕ) {F G R S : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*R^j)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*S^j) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ F*G*(R+S)^h := by
  calc
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (h-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*(F*R^i)*(G*S^(h-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfj i hi') (Nat.cast_nonneg _)
          (mul_nonneg hF (pow_nonneg hR _)))
        (hgj (h-i) (Nat.sub_le _ _))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg hG (pow_nonneg hS _))
    _ = F*G*(R+S)^h := by
      rw [add_pow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem weighted_quotient_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f d : E → ℝ} (hf : ContDiff ℝ ∞ f) (hd : ContDiff ℝ ∞ d)
    (hdne : ∀ y, d y ≠ 0) (x : E) (h : ℕ)
    {δ W M N R S : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hS : 0 ≤ S) (hx : δ*W^2 ≤ d x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ N*R^j*W^2)
    (hdj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j d x‖ ≤ M*S^j*W^2) :
    ‖iteratedFDeriv ℝ h (fun y => f y/d y) x‖ ≤
      N*(h.factorial : ℝ)^2/δ*(R+max 1 (M/δ)*S)^h := by
  have hrec : ContDiff ℝ ∞ (fun y => 1/d y) := contDiff_const.div hd hdne
  have hinv : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => 1/d y) x‖ ≤
      ((h.factorial:ℝ)^2/(δ*W^2))*(max 1 (M/δ)*S)^j := by
    intro j hj
    have hb := weighted_reciprocal_jet_bound hd j hδ hW hS hx
      (fun i hi hij => hdj i hi (hij.trans hj))
    calc
      _ ≤ (j.factorial:ℝ)^2*(max 1 (M/δ)*S)^j/(δ*W^2) := hb
      _ ≤ (h.factorial:ℝ)^2*(max 1 (M/δ)*S)^j/(δ*W^2) := by
        gcongr
      _ = _ := by ring
  have hb := geometric_product_jet_bound hf hrec x h
    (F:=N*W^2) (G:=(h.factorial:ℝ)^2/(δ*W^2))
    (mul_nonneg hN (sq_nonneg _)) (by positivity) hR
    (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hS)
    (fun j hj => by simpa only [mul_assoc,mul_left_comm,mul_comm] using hfj j hj) hinv
  have he : (N*W^2)*((h.factorial:ℝ)^2/(δ*W^2)) = N*(h.factorial:ℝ)^2/δ := by
    field_simp
  simpa only [one_div,← div_eq_mul_inv,he] using hb

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormIteratedFDerivScalarDirection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma norm_iteratedFDeriv_scalar_direction {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (v : E) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (k+1) f x‖ := by
  have h : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hb := norm_iteratedFDeriv_clm_apply_const (c := v) (x := x) h.contDiffAt
    (show (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
  simpa only [norm_iteratedFDeriv_fderiv] using hb



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SmoothExtension
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
namespace YauCounterexamples

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

lemma smooth_extension_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f O) :
    ∃ F : E → F, ContDiff ℝ ∞ F ∧ f =ᶠ[𝓝 x] F := by
  obtain ⟨F,hF,he⟩ := smooth_extension_near_compact isCompact_singleton hO
    (singleton_subset_iff.mpr hx) hf
  exact ⟨F,hF,he.filter_mono (nhds_le_nhdsSet (mem_singleton x))⟩

lemma positive_smooth_extension_at {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hfx : 0 < f x) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ (∀ y, 0 < F y) ∧ f =ᶠ[𝓝 x] F := by
  have hp : {y | 0 < f y} ∈ 𝓝 x :=
    (hf.continuousOn.continuousAt (hO.mem_nhds hx)).eventually (isOpen_Ioi.mem_nhds hfx)
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hp
  obtain ⟨F,hF,he⟩ := smooth_extension_at (hO.inter hVo) ⟨hx,hxV⟩
    ((hf.mono inter_subset_left).log (fun y hy => (hV hy.2).ne'))
  refine ⟨fun y => Real.exp (F y), hF.exp,fun _ => Real.exp_pos _,?_⟩
  filter_upwards [he, hp] with y hy hpy
  rw [← hy,Real.exp_log hpy]

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
open scoped Topology ContDiff InnerProductSpace Matrix
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

lemma roundPower_smooth (a b : Euclidean (d+1)) (k : ℕ) :
    ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ (roundPower a b k) := by
  have hc : ContDiff ℝ ∞ (fun x : Euclidean (d+1) => (planarLinear a b x)^k) :=
    (planarLinear a b).contDiff.pow k
  exact (Complex.reCLM.contDiff.comp hc).contMDiff.comp contMDiff_coe_sphere


end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateGradientPairScalarCorrection
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
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
section GradientPairCalculus
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_symm (g : SmoothMetric E M) (u v : M → ℝ) (x : M) :
    coordinateGradientPair g u v x = coordinateGradientPair g v u x := by
  have hs (i j : CoordIndex E) : (metricCoefficients g x ((chartAt E x) x))⁻¹ j i =
      (metricCoefficients g x ((chartAt E x) x))⁻¹ i j := by
    have h := congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A i j)
      (metricCoefficients_posDef g x ((chartAt E x).map_source (mem_chart_source E x))).inv.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  unfold coordinateGradientPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs]
  ring

end GradientPairCalculus

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
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_mul_left {f u : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (v : M → ℝ) (g : SmoothMetric E M) (x : M) :
    coordinateGradientPair g (fun y => f y * u y) v x =
      f x * coordinateGradientPair g u v x + u x * coordinateGradientPair g f v x := by
  let c := chartAt E x
  have hx := c.map_source (mem_chart_source E x)
  have hf' := (contDiffAt_inChart hf x hx).differentiableAt (by simp)
  have hu' := (contDiffAt_inChart hu x hx).differentiableAt (by simp)
  have he : ((fun y => f y * u y) ∘ c.symm) =
      fun y => (f ∘ c.symm) y * (u ∘ c.symm) y := rfl
  unfold coordinateGradientPair
  change (∑ i, ∑ j, _ * fderiv ℝ ((fun y => f y * u y) ∘ c.symm) (c x) _ * _) = _
  rw [he]
  erw [fderiv_fun_mul hf' hu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    Function.comp_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [c]
  rw [(chartAt E x).left_inv (mem_chart_source E x)]
  ring



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartGradientProjectionSmooth
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
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma chartGradientField_smooth {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    (i : CoordIndex E) :
    ContDiffOn ℝ ∞ (chartGradientField g u p i) (chartAt E p).target := by
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  unfold chartGradientField coordinateFlux
  apply ContDiffAt.sum
  intro j _
  exact ((contDiffOn_metricInverse g p i j).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).mul
    (((contDiffAt_inChart hu p hy).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const)

lemma coordinateGradientPair_nonneg (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    0 ≤ coordinateGradientPair g u u x := by
  have hp := (metricCoefficients_posDef g x
    ((chartAt E x).map_source (mem_chart_source E x))).inv.posSemidef.dotProduct_mulVec_nonneg
    (fun i => fderiv ℝ (u ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E i))
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at hp
  convert hp using 1; try rfl
  unfold coordinateGradientPair
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma geometric_product_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (h : ℕ) {F G R S : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*R^j)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*S^j) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ F*G*(R+S)^h := by
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hx hf
  obtain ⟨g',hg',hge⟩ := smooth_extension_at hO hx hg
  have hb := geometric_product_jet_bound hf' hg' x h hF hG hR hS
    (fun j hj => (hfe.iteratedFDeriv ℝ j).self_of_nhds ▸ hfj j hj)
    (fun j hj => (hge.iteratedFDeriv ℝ j).self_of_nhds ▸ hgj j hj)
  change ‖iteratedFDeriv ℝ h (f*g) x‖ ≤ _
  rw [(hfe.mul hge).iteratedFDeriv ℝ h |>.self_of_nhds]
  exact hb

lemma norm_iteratedFDeriv_scalar_direction_on {O : Set E} (hO : IsOpen O)
    {x : E} (hx : x ∈ O) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (v : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y v) x‖ ≤
      ‖v‖*‖iteratedFDeriv ℝ (k+1) f x‖ := by
  obtain ⟨F,hF,he⟩ := smooth_extension_at hO hx hf
  have hd : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 x] (fun y => fderiv ℝ F y v) :=
    (he.fderiv (𝕜:=ℝ)).mono (fun y hy => congrArg (fun L : E →L[ℝ] ℝ => L v) hy)
  rw [(hd.iteratedFDeriv ℝ k).self_of_nhds, (he.iteratedFDeriv ℝ (k+1)).self_of_nhds]
  exact norm_iteratedFDeriv_scalar_direction hF v k x

lemma chartGradientField_jet_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    {y : E} (hy : y ∈ (chartAt E p).target) (h : ℕ) {n W C A : ℝ}
    (hn : 1 ≤ n) (hW : 0 < W) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (haj : ∀ i j, ∀ k ≤ h, ‖iteratedFDeriv ℝ k
      (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A)
    (huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt E p).symm) y‖ ≤ C*n^(k+4)*W) :
    ∀ i, ∀ k ≤ h, ‖iteratedFDeriv ℝ k (chartGradientField g u p i) y‖ ≤
      (2^h*A*C*(∑ j, ‖Module.finBasis ℝ E j‖))*n^(k+5)*W := by
  let U := u ∘ (chartAt E p).symm
  have hU : ContDiffOn ℝ ∞ U (chartAt E p).target :=
    fun z hz => (contDiffAt_inChart hu p hz).contDiffWithinAt
  have hdi (j : CoordIndex E) : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ U z (Module.finBasis ℝ E j)) (chartAt E p).target := by
    intro z hz
    exact (((contDiffAt_inChart hu p hz).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const).contDiffWithinAt
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  intro i k hk
  have hprod (j : CoordIndex E) :
      ‖iteratedFDeriv ℝ k (fun z => (metricCoefficients g p z)⁻¹ i j *
        fderiv ℝ U z (Module.finBasis ℝ E j)) y‖ ≤
      (2^h*A*C*‖Module.finBasis ℝ E j‖)*n^(k+5)*W := by
    have hder (l : ℕ) (hl : l ≤ k) :
        ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ U z (Module.finBasis ℝ E j)) y‖ ≤
          ‖Module.finBasis ℝ E j‖*C*n^5*W*n^l := by
      calc
        _ ≤ ‖Module.finBasis ℝ E j‖*‖iteratedFDeriv ℝ (l+1) U y‖ :=
          norm_iteratedFDeriv_scalar_direction_on (chartAt E p).open_target hy hU _ _
        _ ≤ ‖Module.finBasis ℝ E j‖*(C*n^((l+1)+4)*W) :=
          mul_le_mul_of_nonneg_left (huj (l+1) (by omega)) (norm_nonneg _)
        _ = _ := by rw [show l+1+4=5+l by omega,pow_add]; ring
    apply (geometric_product_jet_bound_on (chartAt E p).open_target hy
      (contDiffOn_metricInverse g p i j) (hdi j) k hA
      (show 0 ≤ ‖Module.finBasis ℝ E j‖*C*n^5*W by positivity) hn0 hn0
      (fun l hl => (haj i j l (hl.trans hk)).trans (by
        exact le_mul_of_one_le_right hA (one_le_pow₀ hn))) hder).trans
    rw [show n+n=2*n by ring,mul_pow]
    calc
      A*(‖Module.finBasis ℝ E j‖*C*n^5*W)*(2^k*n^k) =
          (2^k*A*C*‖Module.finBasis ℝ E j‖)*n^(k+5)*W := by rw [pow_add]; ring
      _ ≤ _ := by gcongr; norm_num
  unfold chartGradientField coordinateFlux
  rw [iteratedFDeriv_fun_sum_apply (fun j _ =>
    (((contDiffOn_metricInverse g p i j).mul (hdi j)).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j, (2^h*A*C*‖Module.finBasis ℝ E j‖)*n^(k+5)*W :=
      Finset.sum_le_sum (fun j _ => hprod j)
    _ = _ := by simp only [Finset.mul_sum,Finset.sum_mul]


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
open scoped Topology ContDiff
section ProjectionJets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma weighted_quotient_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f d : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hd : ContDiffOn ℝ ∞ d O)
    (h : ℕ) {δ W M N R S : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hS : 0 ≤ S) (hx : δ*W^2 ≤ d x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ N*R^j*W^2)
    (hdj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j d x‖ ≤ M*S^j*W^2) :
    ‖iteratedFDeriv ℝ h (fun y => f y/d y) x‖ ≤
      N*(h.factorial : ℝ)^2/δ*(R+max 1 (M/δ)*S)^h := by
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hxO hf
  obtain ⟨d',hd',hdp,hde⟩ := positive_smooth_extension_at hO hxO hd
    ((by positivity : 0 < δ*W^2).trans_le hx)
  have hq := weighted_quotient_jet_bound hf' hd' (fun y => (hdp y).ne') x h hδ hW
    hN hR hS (hde.self_of_nhds ▸ hx)
    (fun j hj => (hfe.iteratedFDeriv ℝ j).self_of_nhds ▸ hfj j hj)
    (fun j hj hjh => (hde.iteratedFDeriv ℝ j).self_of_nhds ▸ hdj j hj hjh)
  change ‖iteratedFDeriv ℝ h (f/d) x‖ ≤ _
  rw [(hfe.div hde).iteratedFDeriv ℝ h |>.self_of_nhds]
  exact hq

variable {ι : Type*} [Fintype ι]

theorem rankOne_projection_jet_bound_on (X α : ι → E → ℝ)
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    (hX : ∀ i, ContDiffOn ℝ ∞ (X i) O) (hα : ∀ i, ContDiffOn ℝ ∞ (α i) O)
    (h : ℕ) {δ W n C B : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hx : δ*W^2 ≤ ∑ i, α i x*X i x)
    (hXj : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ C*n^j*W)
    (hαj : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B*n^j*W)
    (i j : ι) :
    ‖iteratedFDeriv ℝ h
      (fun y => X i y*α j y/(∑ l, α l y*X l y)) x‖ ≤
      (C*B*(h.factorial:ℝ)^2/δ*
        (2+2*max 1 ((Fintype.card ι:ℝ)*C*B/δ))^h)*n^h := by
  have hprod (i j : ι) (k : ℕ) (hk : k ≤ h) :
      ‖iteratedFDeriv ℝ k (fun y => X i y*α j y) x‖ ≤ C*B*(2*n)^k*W^2 := by
    have hh := geometric_product_jet_bound_on hO hxO (hX i) (hα j) k
      (show 0 ≤ C*W by positivity) (show 0 ≤ B*W by positivity) hn hn
      (fun l hl => by simpa only [mul_assoc,mul_comm,mul_left_comm] using hXj i l (hl.trans hk))
      (fun l hl => by simpa only [mul_assoc,mul_comm,mul_left_comm] using hαj j l (hl.trans hk))
    convert hh using 1 <;> first | rfl | ring
  have hden : ContDiffOn ℝ ∞ (fun y => ∑ l, α l y*X l y) O :=
    ContDiffOn.sum (fun l _ => (hα l).mul (hX l))
  have hdenj (k : ℕ) (_hk : 1 ≤ k) (hk : k ≤ h) :
      ‖iteratedFDeriv ℝ k (fun y => ∑ l, α l y*X l y) x‖ ≤
        ((Fintype.card ι:ℝ)*C*B)*(2*n)^k*W^2 := by
    rw [iteratedFDeriv_fun_sum_apply (fun l _ =>
      (((hα l).mul (hX l)).contDiffAt (hO.mem_nhds hxO)).of_le
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))))]
    calc
      _ ≤ ∑ l : ι, ‖iteratedFDeriv ℝ k (fun y => α l y*X l y) x‖ := norm_sum_le _ _
      _ ≤ ∑ l : ι, C*B*(2*n)^k*W^2 := by
        apply Finset.sum_le_sum
        intro l _
        simpa only [mul_comm] using hprod l l k hk
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  have hq := weighted_quotient_jet_bound_on hO hxO ((hX i).mul (hα j)) hden h hδ hW
    (mul_nonneg hC hB) (show 0 ≤ 2*n by positivity) (show 0 ≤ 2*n by positivity)
    hx (hprod i j) hdenj
  convert hq using 1
  all_goals try with_reducible_and_instances rfl
  rw [show 2*n+max 1 ((Fintype.card ι:ℝ)*C*B/δ)*(2*n) =
    (2+2*max 1 ((Fintype.card ι:ℝ)*C*B/δ))*n by ring,mul_pow]
  ring
end ProjectionJets

open scoped Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma chartGradientField_sharp_jet_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    {y : E} (hy : y ∈ (chartAt E p).target) (h : ℕ) {n W C A : ℝ}
    (hn : 1 ≤ n) (hW : 0 < W) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (haj : ∀ i j, ∀ k ≤ h, ‖iteratedFDeriv ℝ k
      (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A)
    (huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt E p).symm) y‖ ≤ C*n^k*W) :
    ∀ i, ∀ k ≤ h, ‖iteratedFDeriv ℝ k (chartGradientField g u p i) y‖ ≤
      (2^h*A*C*(∑ j, ‖Module.finBasis ℝ E j‖))*n^k*(n*W) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hh := chartGradientField_jet_bound hu g p hy h hn
    (show 0 < W/n^4 by positivity) hC hA haj
    (fun k hk => (huj k hk).trans_eq (by rw [pow_add]; field_simp))
  intro i k hk
  apply (hh i k hk).trans_eq
  rw [show k+5=k+1+4 by omega,pow_add,pow_succ]
  field_simp

theorem chartGradientProjection_jet_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    {y : E} (hy : y ∈ (chartAt E p).target) (h : ℕ) {δ n W C A L : ℝ}
    (hδ : 0 < δ) (hn : 1 ≤ n) (hW : 0 < W)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (he : ∀ i, ‖Module.finBasis ℝ E i‖ ≤ L)
    (haj : ∀ i j, ∀ k ≤ h, ‖iteratedFDeriv ℝ k
      (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A)
    (huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt E p).symm) y‖ ≤ C*n^k*W)
    (hgrad : δ*(n*W)^2 ≤ coordinateGradientPair g u u ((chartAt E p).symm y)) :
    let K := 2^h*A*C*(∑ j, ‖Module.finBasis ℝ E j‖)
    ∀ i j, ‖iteratedFDeriv ℝ h (chartGradientProjection g u p i j) y‖ ≤
      (K*(C*L)*(h.factorial:ℝ)^2/δ*
        (2+2*max 1 ((Fintype.card (CoordIndex E):ℝ)*K*(C*L)/δ))^h)*n^h := by
  intro K i j
  let α := fun i z => fderiv ℝ (u ∘ (chartAt E p).symm) z (Module.finBasis ℝ E i)
  have hα (i : CoordIndex E) : ContDiffOn ℝ ∞ (α i) (chartAt E p).target := by
    intro z hz
    exact (((contDiffAt_inChart hu p hz).fderiv_right (m:=∞) (by simp)).clm_apply
      contDiffAt_const).contDiffWithinAt
  have hU : ContDiffOn ℝ ∞ (u ∘ (chartAt E p).symm) (chartAt E p).target :=
    fun z hz => (contDiffAt_inChart hu p hz).contDiffWithinAt
  have hαj (i : CoordIndex E) (k : ℕ) (hk : k ≤ h) :
      ‖iteratedFDeriv ℝ k (α i) y‖ ≤ (C*L)*n^k*(n*W) := by
    calc
      _ ≤ ‖Module.finBasis ℝ E i‖*‖iteratedFDeriv ℝ (k+1) (u ∘ (chartAt E p).symm) y‖ :=
        norm_iteratedFDeriv_scalar_direction_on (chartAt E p).open_target hy hU _ _
      _ ≤ L*(C*n^(k+1)*W) := mul_le_mul (he i) (huj (k+1) (by omega))
        (norm_nonneg _) hL
      _ = _ := by rw [pow_succ]; ring
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpair (z : E) : localGradientPair g u u p z =
      ∑ l, α l z*chartGradientField g u p l z := rfl
  have hg : δ*(n*W)^2 ≤ ∑ l, α l y*chartGradientField g u p l y := by
    rw [coordinateGradientPair_inChart hu hu g p _ ((chartAt E p).map_target hy),
      (chartAt E p).right_inv hy,hpair] at hgrad
    exact hgrad
  have hh := rankOne_projection_jet_bound_on (chartGradientField g u p) α
    (chartAt E p).open_target hy (chartGradientField_smooth hu g p) hα h hδ
    (mul_pos (zero_lt_one.trans_le hn) hW) (zero_le_one.trans hn) hK
    (mul_nonneg hC hL) hg (chartGradientField_sharp_jet_bound hu g p hy h hn hW hC hA haj huj)
    hαj i j
  have hfun : chartGradientProjection g u p i j =
      (fun z => chartGradientField g u p i z*α j z/(∑ l, α l z*chartGradientField g u p l z)) := by
    funext z
    rw [chartGradientProjection,hpair]
  rw [hfun]
  exact hh

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
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma sharp_conjugate_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f w : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hw : ContDiffOn ℝ ∞ w O)
    (h : ℕ) {δ W n C D : ℝ} (hδ : 0 < δ) (hW : 0 < W) (hn : 1 ≤ n)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hx : δ ≤ w x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ C*n^j*W)
    (hwj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j w x‖ ≤ D) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y/w y) x‖ ≤
      (C*(h.factorial:ℝ)^2/δ*(1+max 1 (D/δ))^h)*n^j*W := by
  intro j hj
  have hh := weighted_quotient_jet_bound_on hO hxO hf hw j hδ zero_lt_one
    (show 0 ≤ C*W by positivity) (zero_le_one.trans hn) (zero_le_one.trans hn)
    (by simpa only [one_pow,mul_one] using hx)
    (fun k hk => by simpa only [one_pow,mul_one,mul_assoc,mul_comm,mul_left_comm] using
        (hfj k (hk.trans hj))) (fun k hk hkj => by
      calc
        _ ≤ D := hwj k hk (hkj.trans hj)
        _ ≤ D*n^k*1^2 := by
          simpa only [one_pow,mul_one] using
            (le_mul_of_one_le_right hD (one_le_pow₀ hn)))
  have hp : (j.factorial:ℝ)^2 ≤ (h.factorial:ℝ)^2 := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast Nat.factorial_le hj
  have hR : 1 ≤ 1+max 1 (D/δ) := by have := le_max_left (1:ℝ) (D/δ); linarith
  calc
    _ ≤ (C*W)*(j.factorial:ℝ)^2/δ*(n+max 1 (D/δ)*n)^j := hh
    _ = (C*(j.factorial:ℝ)^2/δ*(1+max 1 (D/δ))^j)*n^j*W := by
      rw [show n+max 1 (D/δ)*n=(1+max 1 (D/δ))*n by ring,mul_pow]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hW.le
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hn) _)
      exact mul_le_mul
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) hδ.le)
        (pow_le_pow_right₀ hR hj) (pow_nonneg (zero_le_one.trans hR) _)
        (div_nonneg (mul_nonneg hC (sq_nonneg _)) hδ.le)

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
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix


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
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}
lemma round_metricCoefficients_at (g : SmoothMetric (Euclidean d) (Sphere d)) (p : Sphere d)
    (hg : ∀ (v w : TangentSpace 𝓘(ℝ,Euclidean d) p),
      g.inner p v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p w)) :
    metricCoefficients g p 0 = Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)) := by
  have hp : (chartAt (Euclidean d) p).symm 0 = p := by
    simpa only [sphere_chart_center] using (chartAt (Euclidean d) p).left_inv (mem_chart_source _ p)
  have hg' : ∀ (v w : TangentSpace 𝓘(ℝ,Euclidean d) ((chartAt (Euclidean d) p).symm 0)),
      g.inner ((chartAt (Euclidean d) p).symm 0) v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) ((chartAt (Euclidean d) p).symm 0) v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) ((chartAt (Euclidean d) p).symm 0) w) := by
    change (fun q : Sphere d => ∀ v w : TangentSpace 𝓘(ℝ,Euclidean d) q,
      g.inner q v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) q v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) q w))
      ((chartAt (Euclidean d) p).symm 0)
    rw [hp]
    exact hg
  let : ContinuousSMul ℝ (Euclidean d) := IsBoundedSMul.continuousSMul
  let : ContinuousSMul ℝ (Euclidean (d+1)) := IsBoundedSMul.continuousSMul
  have hround : fderiv ℝ (roundChart (p : Euclidean (d+1)) (sphereFrame p)) 0 =
      (sphereFrame p).toContinuousLinearMap :=
    (roundChart_first (p : Euclidean (d+1)) (sphereFrame p)).fderiv
  ext i j
  rw [metricCoefficients,hg']
  rw [coordinateVector,coordinateVector,sphere_coordinate_embedding p 0,
    sphere_coordinate_embedding p 0,hround]
  exact (sphereFrame p).inner_map_map _ _
lemma roundPower_coordinateGradientPair (g : SmoothMetric (Euclidean d) (Sphere d)) (p : Sphere d)
    (hg : ∀ (v w : TangentSpace 𝓘(ℝ,Euclidean d) p),
      g.inner p v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p w))
    (a b : Euclidean (d+1)) (n : ℕ) (hn : 1 ≤ n)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    coordinateGradientPair g (roundPower a b n) (roundPower a b n) p =
      (n:ℝ)^2 * ((Complex.normSq (planarLinear a b p))^(n-1) - (roundPower a b n p)^2) := by
  rw [coordinateGradientPair,sphere_chart_center,round_metricCoefficients_at g p hg]
  convert roundPower_gradient_square a b n hn ha hb hab p using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring



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
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ScalarCauchyCross
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open Set Filter
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma coordinateGradientPair_cauchy (g : SmoothMetric E M) (u v : M → ℝ) (x : M) :
    coordinateGradientPair g u v x ^ 2 ≤
      coordinateGradientPair g u u x * coordinateGradientPair g v v x := by
  let c := chartAt E x
  let a := (metricCoefficients g x (c x))⁻¹
  let du := fun i => fderiv ℝ (u ∘ c.symm) (c x) (Module.finBasis ℝ E i)
  let dv := fun i => fderiv ℝ (v ∘ c.symm) (c x) (Module.finBasis ℝ E i)
  have hp := (metricCoefficients_posDef g x (c.map_source (mem_chart_source E x))).inv
  have he (f h : M → ℝ) : coordinateGradientPair g f h x =
      (fun i => fderiv ℝ (f ∘ c.symm) (c x) (Module.finBasis ℝ E i)) ⬝ᵥ
        (a *ᵥ (fun i => fderiv ℝ (h ∘ c.symm) (c x) (Module.finBasis ℝ E i))) := by
    simp only [coordinateGradientPair,dotProduct,Matrix.mulVec,Finset.mul_sum,a,c]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he u v,he u u,he v v]
  exact real_matrix_cauchy hp.posSemidef du dv

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

lemma scalar_cauchy_cross {a b c X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hc : c^2 ≤ X*Y) : 2*a*b*c ≤ a^2*X+b^2*Y := by
  have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg (a*b))
  apply le_of_sq_le_sq _ (by positivity)
  nlinarith [sq_nonneg (a^2*X-b^2*Y)]

lemma coordinateGradientPair_mul_self_le {E M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    {f u : M → ℝ} (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (g : SmoothMetric E M) (x : M) :
    coordinateGradientPair g (fun y => f y*u y) (fun y => f y*u y) x ≤
      2*(f x)^2*coordinateGradientPair g u u x + 2*(u x)^2*coordinateGradientPair g f f x := by
  have hc := scalar_cauchy_cross (a:=f x) (b:=u x)
    (coordinateGradientPair_nonneg g u x) (coordinateGradientPair_nonneg g f x)
    (coordinateGradientPair_cauchy g u f x)
  rw [coordinateGradientPair_mul_left hf hu,
    coordinateGradientPair_symm g u (fun y => f y*u y) x,
    coordinateGradientPair_symm g f (fun y => f y*u y) x,
    coordinateGradientPair_mul_left hf hu,
    coordinateGradientPair_mul_left hf hu,
    coordinateGradientPair_symm g f u x]
  nlinarith

lemma annular_conjugate_gradient_lower (n : ℕ) (hn : 1 ≤ n)
    {R t U u w Gu Gw : ℝ} (hR : 0 < R) (hRt : R ≤ t) (ht : t < 1)
    (hU : U^2 ≤ R^n) (he : U=w*u) (hwl : 1/2 ≤ w) (hwu : w ≤ 2)
    (hGu : 0 ≤ Gu) (hGw : 0 ≤ Gw) (hGws : Gw ≤ (1-t)/16)
    (hgrad : (n:ℝ)^2*(R^(n-1)-U^2) ≤ 2*w^2*Gu+2*u^2*Gw) :
    (1-t)/16*(n:ℝ)^2*R^n ≤ Gu := by
  have hnR : 1 ≤ (n:ℝ)^2 := by
    have hh : 1 ≤ (n:ℝ) := by exact_mod_cast hn
    nlinarith
  have hR1 : R ≤ 1 := hRt.trans ht.le
  have hRp : 0 < R^(n-1) := pow_pos hR _
  have hRn : R^n=R^(n-1)*R := by rw [←pow_succ,Nat.sub_add_cancel hn]
  have hstep : R^n ≤ R^(n-1) := by rw [hRn]; nlinarith [mul_le_mul_of_nonneg_left hR1 hRp.le]
  have hdiff : (1-t)*R^n ≤ R^(n-1)-U^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hRt hRp.le
    have h₂ := mul_le_mul_of_nonneg_left hstep (sub_pos.mpr ht).le
    rw [hRn] at hU
    nlinarith
  have hwwl : 1/4 ≤ w^2 := by nlinarith
  have hwwu : w^2 ≤ 4 := by nlinarith
  have huu : u^2 ≤ 4*R^n := by
    have hh := mul_le_mul_of_nonneg_right hwwl (sq_nonneg u)
    rw [he] at hU
    nlinarith
  have hsmall : 2*u^2*Gw ≤ (1-t)/2*R^n := by
    have hh := mul_le_mul huu hGws hGw (by positivity : 0 ≤ 4*R^n)
    nlinarith
  have hbig : 2*w^2*Gu ≤ 8*Gu := by nlinarith [mul_le_mul_of_nonneg_right hwwu hGu]
  have hlower := mul_le_mul_of_nonneg_left hdiff (sq_nonneg (n:ℝ))
  have hfreq := mul_le_mul_of_nonneg_right hnR (mul_nonneg (sub_pos.mpr ht).le (pow_nonneg hR.le n))
  nlinarith

variable {d : ℕ}

theorem roundPower_conjugate_gradient_lower
    (g : SmoothMetric (Euclidean d) (Sphere d)) (p : Sphere d)
    (hg : ∀ v z : TangentSpace 𝓘(ℝ,Euclidean d) p,
      g.inner p v z = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p z))
    (a b : Euclidean (d+1)) (n : ℕ) (hn : 1 ≤ n)
    (ha : inner ℝ a a=1) (hb : inner ℝ b b=1) (hab : inner ℝ a b=0)
    {t : ℝ} (hR : 0 < Complex.normSq (planarLinear a b p))
    (hRt : Complex.normSq (planarLinear a b p) ≤ t) (ht : t < 1)
    (w : Sphere d → ℝ) (hw : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ w)
    (hw0 : ∀ x, w x ≠ 0) (hwl : 1/2 ≤ w p) (hwu : w p ≤ 2)
    (hG : coordinateGradientPair g w w p ≤ (1-t)/16) :
    (1-t)/16*(n:ℝ)^2*Complex.normSq (planarLinear a b p)^n ≤
      coordinateGradientPair g (fun x => roundPower a b n x/w x)
        (fun x => roundPower a b n x/w x) p := by
  let u := fun x => roundPower a b n x/w x
  have hU := roundPower_smooth a b n
  have hu : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ u := hU.div₀ hw hw0
  have he : roundPower a b n = fun x => w x*u x := by funext x; dsimp [u]; field_simp [hw0 x]
  have hupper := coordinateGradientPair_mul_self_le hw hu g p
  rw [←he,roundPower_coordinateGradientPair g p hg a b n hn ha hb hab] at hupper
  exact annular_conjugate_gradient_lower n hn hR hRt ht
    (complex_power_real_sq_bound (planarLinear a b p) n) (congrFun he p) hwl hwu
    (coordinateGradientPair_nonneg g u p) (coordinateGradientPair_nonneg g w p) hG hupper


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactMetricInverseJets
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
open Set Filter Function
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma geometric_complex_product_jet_bound
    {f g : E → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (h : ℕ) {F G R S : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*R^j)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*S^j) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ F*G*(R+S)^h := by
  calc
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (h-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*(F*R^i)*(G*S^(h-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfj i hi') (Nat.cast_nonneg _)
          (mul_nonneg hF (pow_nonneg hR _)))
        (hgj (h-i) (Nat.sub_le _ _))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg hG (pow_nonneg hS _))
    _ = F*G*(R+S)^h := by
      rw [add_pow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma compact_raw_jet_bound {O K : Set E} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) {f : E → F} (hf : ContDiffOn ℝ ∞ f O) (h : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ h, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hb (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    intro x hx
    exact (((hf.contDiffAt (hO.mem_nhds (hKO hx))).continuousAt_iteratedFDeriv
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))))).continuousWithinAt
  choose B hB using hb
  let C := 1+∑ j ∈ Finset.range (h+1), max 0 (B j)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  refine ⟨C,hC,?_⟩
  intro j hj x hx
  calc
    _ ≤ B j := hB j x hx
    _ ≤ max 0 (B j) := le_max_right _ _
    _ ≤ ∑ j ∈ Finset.range (h+1), max 0 (B j) :=
      Finset.single_le_sum (fun k _ => le_max_left _ _) (Finset.mem_range.mpr (by omega))
    _ ≤ C := by dsimp [C]; linarith


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
open scoped Topology ContDiff
section PowerJets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma complex_power_jet_bound {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : E) (h n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ ‖f x‖*(C)^j) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y^n) x‖ ≤
      ‖f x‖^n*((n:ℝ)*C)^j := by
  induction n with
  | zero =>
    intro j hj
    cases j with
    | zero => simp only [pow_zero,norm_iteratedFDeriv_zero,norm_one,one_mul,le_refl]
    | succ j => simp only [pow_zero,iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,
        Nat.cast_zero,zero_mul,zero_pow (by omega : j+1 ≠ 0),mul_zero,le_refl]
  | succ n ih =>
    intro j hj
    have hb := geometric_complex_product_jet_bound (hf.pow n) hf x j
      (pow_nonneg (norm_nonneg _) _) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC) hC
      (fun k hk => ih k (hk.trans hj)) (fun k hk => hfj k (hk.trans hj))
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hb
end PowerJets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem annular_real_power_jets {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f O) (h n : ℕ) {r C : ℝ}
    (hr : 0 < r) (hrx : r ≤ ‖f x‖) (hC : 0 ≤ C)
    (hfj : ∀ j, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j f x‖ ≤ C) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (f y^n).re) x‖ ≤
      (max 1 (C/r))^j*(n:ℝ)^j*‖f x‖^n := by
  let B := max 1 (C/r)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hbound : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ ‖f x‖*B^j := by
    intro j hj
    by_cases hj0 : j=0
    · subst j
      rw [norm_iteratedFDeriv_zero,pow_zero,mul_one]
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hbj : B ≤ B^j := by simpa only [pow_one] using pow_le_pow_right₀ hB1 hj1
      calc
        _ ≤ C := hfj j hj1 hj
        _ = r*(C/r) := by field_simp
        _ ≤ ‖f x‖*B^j := mul_le_mul hrx ((le_max_right _ _).trans hbj)
          (div_nonneg hC hr.le) (norm_nonneg _)
  obtain ⟨F,hF,he⟩ := smooth_extension_at hO hxO hf
  have hpow := complex_power_jet_bound hF x h n hB0 (fun j hj => by
    rw [←he.self_of_nhds,←(he.iteratedFDeriv ℝ j).self_of_nhds]
    exact hbound j hj)
  intro j hj
  have hp := ContinuousLinearMap.norm_iteratedFDeriv_comp_left Complex.reCLM (x:=x)
    (hF.pow n).contDiffAt (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
  have heRe : (fun y => (f y^n).re) =ᶠ[𝓝 x] (fun y => (F y^n).re) :=
    he.mono (fun y hy => congrArg (fun z : ℂ => (z^n).re) hy)
  rw [(heRe.iteratedFDeriv ℝ j).self_of_nhds]
  calc
    _ ≤ ‖Complex.reCLM‖*‖iteratedFDeriv ℝ j (fun y => F y^n) x‖ := hp
    _ ≤ 1*(‖F x‖^n*((n:ℝ)*B)^j) := mul_le_mul (le_of_eq Complex.reCLM_norm)
      (hpow j hj) (norm_nonneg _) zero_le_one
    _ = _ := by rw [←he.self_of_nhds,mul_pow]; dsimp [B]; ring

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

variable {d : ℕ}

theorem roundPower_annular_chart_jets (a b : Euclidean (d+1)) (p : Sphere d)
    {K : Set (Euclidean d)} (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean d) p).target)
    (h : ℕ) {r : ℝ} (hr : 0 < r) (hKr : ∀ y ∈ K, r ≤ ‖roundPlanarChart a b p y‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) y‖ ≤
        C*(n:ℝ)^j*‖roundPlanarChart a b p y‖^n := by
  have hf := roundPlanarChart_smooth a b p
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound (chartAt (Euclidean d) p).open_target hK hKO hf h
  let B := max 1 (D/r)
  have hB1 : 1 ≤ B := le_max_left _ _
  refine ⟨B^h,pow_pos (zero_lt_one.trans_le hB1) _,?_⟩
  intro n y hy j hj
  have hh := annular_real_power_jets (chartAt (Euclidean d) p).open_target (hKO hy) hf h n
    hr (hKr y hy) (zero_le_one.trans hD) (fun k _ hk => hDj k hk y hy) j hj
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 hj) (pow_nonneg (Nat.cast_nonneg _) _))
    (pow_nonneg (norm_nonneg _) _))

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
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
section CompactInverseJets
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma compact_metric_inverse_jets (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKO : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i j : CoordIndex E, ∀ k ≤ h, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A := by
  classical
  choose B hB hBj using fun i j : CoordIndex E =>
    compact_raw_jet_bound (chartAt E p).open_target hK hKO (contDiffOn_metricInverse g p i j) h
  let A := 1+∑ i, ∑ j, B i j
  have hB0 (i j : CoordIndex E) : 0 ≤ B i j := zero_le_one.trans (hB i j)
  have hA : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hB0 i j)))
  refine ⟨A,hA,?_⟩
  intro i j k hk y hy
  calc
    _ ≤ B i j := hBj i j k hk y hy
    _ ≤ ∑ j, B i j := Finset.single_le_sum (fun j _ => hB0 i j) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, B i j := Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg (fun j _ => hB0 i j)) (Finset.mem_univ i)
    _ ≤ A := by dsimp [A]; linarith
end CompactInverseJets


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RoundPowerConjugateProjectionUniform
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
variable {d : ℕ}
theorem roundPower_conjugate_projection_uniform_oai
    (g : SmoothMetric (Euclidean d) (Sphere d)) (a b : Euclidean (d+1)) (p : Sphere d)
    (ha : inner ℝ a a=1) (hb : inner ℝ b b=1) (hab : inner ℝ a b=0)
    {K : Set (Euclidean d)} (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean d) p).target)
    (hg : ∀ y ∈ K, ∀ v z : TangentSpace 𝓘(ℝ,Euclidean d) ((chartAt (Euclidean d) p).symm y),
      g.inner _ v z = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
          (fun q : Sphere d => (q : Euclidean (d+1))) _ v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
          (fun q : Sphere d => (q : Euclidean (d+1))) _ z))
    (h : ℕ) {r t D : ℝ} (hr : 0 < r) (ht : t < 1) (hD : 0 ≤ D)
    (hKr : ∀ y ∈ K, r ≤ ‖roundPlanarChart a b p y‖)
    (hKt : ∀ y ∈ K, Complex.normSq (roundPlanarChart a b p y) ≤ t)
    : ∃ C : ℝ, 0 < C ∧ ∀ (w : Sphere d → ℝ),
      ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ w →
      (∀ x, w x ≠ 0) →
      (∀ y ∈ K, 1/2 ≤ w ((chartAt (Euclidean d) p).symm y)) →
      (∀ y ∈ K, w ((chartAt (Euclidean d) p).symm y) ≤ 2) →
      (∀ j : ℕ, 1 ≤ j → j ≤ h+1 → ∀ y ∈ K,
        ‖iteratedFDeriv ℝ j (w ∘ (chartAt (Euclidean d) p).symm) y‖ ≤ D) →
      (∀ y ∈ K, coordinateGradientPair g w w ((chartAt (Euclidean d) p).symm y) ≤ (1-t)/16) →
    ∀ n : ℕ, 1 ≤ n → ∀ y ∈ K, ∀ i j : CoordIndex (Euclidean d),
      ‖iteratedFDeriv ℝ h (chartGradientProjection g
        (fun x => roundPower a b n x/w x) p i j) y‖ ≤ C*(n:ℝ)^h := by
  obtain ⟨C0,hC0,hCj⟩ := roundPower_annular_chart_jets a b p hK hKO (h+1) hr hKr
  obtain ⟨A,hA,hAj⟩ := compact_metric_inverse_jets g p hK hKO h
  let C1 := C0*((h+1).factorial:ℝ)^2/(1/2)*(1+max 1 (D/(1/2)))^(h+1)
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  let L := ∑ j, ‖Module.finBasis ℝ (Euclidean d) j‖
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have he (i : CoordIndex (Euclidean d)) : ‖Module.finBasis ℝ (Euclidean d) i‖ ≤ L :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  let δ := (1-t)/16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let J := 2^h*A*C1*L
  let C := J*(C1*L)*(h.factorial:ℝ)^2/δ*
    (2+2*max 1 ((Fintype.card (CoordIndex (Euclidean d)):ℝ)*J*(C1*L)/δ))^h
  refine ⟨max C 1,zero_lt_one.trans_le (le_max_right _ _),?_⟩
  intro w hw hw0 hwl hwu hwj hwG n hn y hy i j
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  let W := ‖roundPlanarChart a b p y‖^n
  have hrY : 0 < ‖roundPlanarChart a b p y‖ := hr.trans_le (hKr y hy)
  have hW : 0 < W := pow_pos hrY _
  let u := fun x => roundPower a b n x/w x
  have hu : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ u :=
    (roundPower_smooth a b n).div₀ (hw) (hw0)
  have huw : ContDiffOn ℝ ∞ (w ∘ (chartAt (Euclidean d) p).symm)
      (chartAt (Euclidean d) p).target := fun z hz => (contDiffAt_inChart (hw) p hz).contDiffWithinAt
  have hu0 : ContDiffOn ℝ ∞ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm)
      (chartAt (Euclidean d) p).target :=
    fun z hz => (contDiffAt_inChart (roundPower_smooth a b n) p hz).contDiffWithinAt
  have huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt (Euclidean d) p).symm) y‖ ≤
      C1*(n:ℝ)^k*W := by
    exact sharp_conjugate_jet_bound_on (chartAt (Euclidean d) p).open_target (hKO hy)
      hu0 huw (h+1) (by norm_num : (0:ℝ)<1/2) hW hnR hC0.le hD (hwl y hy)
      (fun k hk => hCj n y hy k hk) (fun k hk hkh => hwj k hk hkh y hy)
  have hR : 0 < Complex.normSq (roundPlanarChart a b p y) := by
    rw [Complex.normSq_eq_norm_sq]; positivity
  have hgL := roundPower_conjugate_gradient_lower g ((chartAt (Euclidean d) p).symm y)
    (hg y hy) a b n hn ha hb hab hR (hKt y hy) ht (w) (hw) (hw0)
    (hwl y hy) (hwu y hy) (hwG y hy)
  have heW : Complex.normSq (roundPlanarChart a b p y)^n=W^2 := by
    dsimp [W]
    rw [Complex.normSq_eq_norm_sq,←pow_mul,←pow_mul,Nat.mul_comm 2 n]
  have hgrad : δ*((n:ℝ)*W)^2 ≤ coordinateGradientPair g u u ((chartAt (Euclidean d) p).symm y) := by
    change δ*(n:ℝ)^2*Complex.normSq (roundPlanarChart a b p y)^n ≤ _ at hgL
    rw [heW] at hgL
    simpa only [mul_pow,mul_assoc] using hgL
  have hp := chartGradientProjection_jet_bound hu g p (hKO hy) h hδ hnR hW hC1
    (zero_le_one.trans hA) hL he (fun i j k hk => hAj i j k hk y hy) huj hgrad i j
  exact hp.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg (Nat.cast_nonneg _) _))
end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.roundPower_conjugate_projection_uniform_oai := @OAI.YauCounterexamples.roundPower_conjugate_projection_uniform_oai
