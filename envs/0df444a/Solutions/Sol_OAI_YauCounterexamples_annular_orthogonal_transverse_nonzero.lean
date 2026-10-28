-- Prove2me | solution 1 for OAI.YauCounterexamples.annular_orthogonal_transverse_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:23:34.395169+00:00
-- url     : https://prove2.me/submissions/06da87be-40a9-47dd-bac7-60742a219016

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007
import Theorems.Thm_OAI_YauCounterexamples_proportional_eigen_global
import Theorems.Thm_OAI_YauCounterexamples_round_pair_rank_transfer

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ExistsPowerRadius
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
lemma exists_power_radius (n : ℕ) (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    ∃ z : ℂ, Complex.normSq z = r^2 ∧ (z^n).im ≠ 0 := by
  let θ : ℝ := Real.pi / (2 * (n:ℝ))
  let z : ℂ := (r:ℂ) * Complex.exp ((θ:ℂ)*Complex.I)
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hθ : (n:ℝ)*θ = Real.pi/2 := by dsimp [θ]; field_simp
  have hpow : z^n = (r^n:ℝ)*Complex.I := by
    rw [show z = (r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I) from rfl,mul_pow,
      ←Complex.exp_nat_mul]
    have he : (n:ℂ)*((θ:ℂ)*Complex.I) = ((Real.pi/2:ℝ):ℂ)*Complex.I := by
      rw [←mul_assoc,←Complex.ofReal_natCast,←Complex.ofReal_mul,hθ]
    rw [he,Complex.exp_ofReal_mul_I]
    simp
  refine ⟨z,?_,?_⟩
  · rw [show z = (r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I) from rfl,map_mul]
    rw [Complex.normSq_ofReal]
    have he : Complex.normSq (Complex.exp ((θ:ℂ)*Complex.I)) = 1 := by
      rw [Complex.normSq_apply,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [he,mul_one]
    ring
  · rw [hpow]
    simpa only [Complex.mul_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,
      ←Complex.ofReal_pow,Complex.ofReal_re] using (pow_pos hr n).ne'
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma planar_sphere_point (a b c : E)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hc : inner ℝ c c = 1)
    (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (z : ℂ) (hz : Complex.normSq z ≤ 1) :
    ∃ p : E, ‖p‖ = 1 ∧ planarLinear a b p = z := by
  let p := z.re • a + z.im • b + Real.sqrt (1-Complex.normSq z) • c
  have hba : inner ℝ b a = 0 := (real_inner_comm a b).trans hab
  have hca : inner ℝ c a = 0 := (real_inner_comm a c).trans hac
  have hcb : inner ℝ c b = 0 := (real_inner_comm b c).trans hbc
  have hpp : inner ℝ p p = 1 := by
    simp only [p,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
      ha,hb,hc,hab,hac,hbc,hba,hca,hcb,conj_trivial,mul_zero,mul_one,zero_add,add_zero]
    nlinarith [Real.sq_sqrt (sub_nonneg.mpr hz),Complex.normSq_apply z]
  refine ⟨p,?_,?_⟩
  · rw [real_inner_self_eq_norm_sq] at hpp
    nlinarith [norm_nonneg p]
  · simp only [planarLinear_apply,p,inner_add_right,inner_smul_right,
      ha,hb,hab,hac,hbc,hba,mul_one,mul_zero,add_zero,zero_add]
    simpa only [mul_comm Complex.I] using Complex.re_add_im z
end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RectangularFactorization
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology
namespace YauCounterexamples
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem rectangular_factorization {I : Set ℝ} {J : Set W}
    (hIo : IsOpen I) (hJo : IsOpen J) (hJc : IsPreconnected J)
    {w₀ : W} (hw₀ : w₀ ∈ J) (V : ℝ × W → ℝ)
    (hV : ContDiffOn ℝ 2 V (I ×ˢ J))
    (hvert : ∀ s ∈ I, ∀ w ∈ J, ∀ v : W,
      fderiv ℝ V (s,w) (0,v) = 0) :
    ∃ F : ℝ → ℝ, ContDiffOn ℝ 2 F I ∧
      ∀ s ∈ I, ∀ w ∈ J, V (s,w) = F s := by
  let F : ℝ → ℝ := fun s => V (s,w₀)
  refine ⟨F, ?_, ?_⟩
  · exact hV.comp (contDiffOn_id.prodMk contDiffOn_const) (fun s hs => ⟨hs,hw₀⟩)
  intro s hs w hw
  have hd (w : W) (hw : w ∈ J) : DifferentiableAt ℝ V (s,w) :=
    (hV.differentiableOn (by norm_num)).differentiableAt
      ((hIo.prod hJo).mem_nhds ⟨hs,hw⟩)
  have hslice : DifferentiableOn ℝ (fun w : W => V (s,w)) J := by
    intro w hw
    exact ((hd w hw).comp w ((differentiableAt_const s).prodMk differentiableAt_id)).differentiableWithinAt
  have hz : EqOn (fderiv ℝ (fun w : W => V (s,w))) 0 J := by
    intro w hw
    change fderiv ℝ (V ∘ (fun w : W => (s,w))) w = 0
    rw [fderiv_comp w (hd w hw) ((differentiableAt_const s).prodMk differentiableAt_id)]
    ext v
    simpa [(hasFDerivAt_prodMk_right (𝕜:=ℝ) s w).fderiv] using hvert s hs w hw v
  exact hJo.is_const_of_fderiv_eq_zero hJc hslice hz hw hw₀
open Filter Function Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem local_factor_of_kernel {f g : E → ℝ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    (hd : fderiv ℝ f x ≠ 0)
    (hker : ∀ y ∈ U, ∀ v : E, fderiv ℝ f y v = 0 → fderiv ℝ g y v = 0) :
    ∃ (V : Set E) (I : Set ℝ) (F : ℝ → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      IsOpen I ∧ IsPreconnected I ∧ f x ∈ I ∧ ContDiffOn ℝ 2 F I ∧
      MapsTo f V I ∧ EqOn g (F ∘ f) V := by
  let L := fderiv ℝ f x
  have hL : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    apply surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (f := L.toLinearMap) (by simp)
    intro hh
    apply hd
    ext y
    exact DFunLike.congr_fun hh y
  have hfx := (hf x hx).contDiffAt (hU.mem_nhds hx)
  have hs : HasStrictFDerivAt f L x := hfx.hasStrictFDerivAt (by norm_num)
  have hLc : L.ker.ClosedComplemented := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := hs.implicitFunctionDataOfComplemented f L hL hLc
  let e := φ.toOpenPartialHomeomorph
  have hex : x ∈ e.source := φ.pt_mem_toOpenPartialHomeomorph_source
  have hefx (y : E) : (e y).1 = f y := rfl
  have he0 : e x = (f x,0) := by simp [e,φ,ImplicitFunctionData.prodFun]
  have hext : (f x, (0 : L.ker)) ∈ e.target := he0 ▸ e.map_source hex
  have heix : e.symm (f x,0) = x := by rw [←he0]; exact e.left_inv hex
  have hr : ContDiffAt ℝ 2 φ.rightFun φ.pt := by
    exact ((Classical.choose hLc).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hi := φ.contDiffAt_implicitFunction hfx hr (by norm_num)
  change ContDiffAt ℝ 2 e.symm (e x) at hi
  rw [he0] at hi
  have hpre : e.symm ⁻¹' U ∈ 𝓝 (f x,(0:L.ker)) := by
    apply (e.continuousAt_symm hext).tendsto
    rw [heix]
    exact hU.mem_nhds hx
  obtain ⟨r,hrpos,hrsub⟩ := Metric.mem_nhds_iff.mp
    (((hi.eventually (by norm_num)).and (e.open_target.mem_nhds hext)).and hpre)
  let I := ball (f x) r
  let J : Set L.ker := ball 0 r
  let B := I ×ˢ J
  have hBo : IsOpen B := isOpen_ball.prod isOpen_ball
  have hBsub (y : ℝ × L.ker) (hy : y ∈ B) :
      ContDiffAt ℝ 2 e.symm y ∧ y ∈ e.target ∧ e.symm y ∈ U := by
    have hy' : y ∈ ball (f x,(0:L.ker)) r := by
      rw [←ball_prod_same]; exact hy
    have hh := hrsub hy'
    exact ⟨hh.1.1,hh.1.2,hh.2⟩
  let G := g ∘ e.symm
  have hG : ContDiffOn ℝ 2 G B := by
    intro y hy
    exact (((hg _ (hBsub y hy).2.2).contDiffAt (hU.mem_nhds (hBsub y hy).2.2)).comp y
      (hBsub y hy).1).contDiffWithinAt
  have hvertical : ∀ s ∈ I, ∀ w ∈ J, ∀ v : L.ker,
      fderiv ℝ G (s,w) (0,v) = 0 := by
    intro s hs w hw v
    let y : ℝ × L.ker := (s,w)
    have hy : y ∈ B := ⟨hs,hw⟩
    have hyU := (hBsub y hy).2.2
    have hdi := (hBsub y hy).1.differentiableAt (by norm_num)
    have hdf := ((hf _ hyU).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
    have hdg := ((hg _ hyU).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
    have heq : f ∘ e.symm =ᶠ[𝓝 y] Prod.fst := by
      filter_upwards [e.open_target.mem_nhds (hBsub y hy).2.1] with z hz
      exact congrArg Prod.fst (e.right_inv hz)
    have hff : fderiv ℝ f (e.symm y) (fderiv ℝ e.symm y (0,v)) = 0 := by
      have hh := heq.fderiv_eq (𝕜:=ℝ)
      rw [fderiv_comp y hdf hdi] at hh
      rw [fderiv_fst] at hh
      exact congrArg (fun A : (ℝ × L.ker) →L[ℝ] ℝ => A (0,v)) hh
    change fderiv ℝ (g ∘ e.symm) y (0,v) = 0
    rw [fderiv_comp y hdg hdi]
    exact hker _ hyU _ hff
  obtain ⟨F,hF,hGF⟩ := rectangular_factorization (I:=I) (J:=J) isOpen_ball isOpen_ball
    (convex_ball (0:L.ker) r).isPreconnected (mem_ball_self hrpos) G hG hvertical
  let V := e.source ∩ e ⁻¹' B
  have hVo : IsOpen V := e.continuousOn.isOpen_inter_preimage e.open_source hBo
  have hxV : x ∈ V := ⟨hex,by change e x ∈ B; rw [he0]; exact ⟨mem_ball_self hrpos,mem_ball_self hrpos⟩⟩
  have hVU : V ⊆ U := by
    intro y hy
    have hh := (hBsub (e y) hy.2).2.2
    rwa [e.left_inv hy.1] at hh
  refine ⟨V,I,F,hVo,hxV,hVU,isOpen_ball,(convex_ball (f x) r).isPreconnected,
    mem_ball_self hrpos,hF,?_,?_⟩
  · intro y hy
    exact hy.2.1
  · intro y hy
    have hh := hGF (e y).1 hy.2.1 (e y).2 hy.2.2
    change g (e.symm (e y)) = F (f y) at hh
    rwa [e.left_inv hy.1] at hh
end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ScalarCompDirectional
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Manifold
open scoped Topology ContDiff
section ScalarComposition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma scalar_comp_directional {F : ℝ → ℝ} {u : E → ℝ} {x : E}
    (hF : DifferentiableAt ℝ F (u x)) (hu : DifferentiableAt ℝ u x) (v : E) :
    fderiv ℝ (F ∘ u) x v = deriv F (u x) * fderiv ℝ u x v := by
  rw [fderiv_comp x hF hu, ContinuousLinearMap.comp_apply]
  exact fderiv_eq_deriv_mul
lemma scalar_comp_second_directional {F : ℝ → ℝ} {u : E → ℝ} {x : E}
    (hF : ContDiffAt ℝ 2 F (u x)) (hu : ContDiffAt ℝ 2 u x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (F ∘ u) y b) x a =
      deriv (deriv F) (u x) * fderiv ℝ u x a * fderiv ℝ u x b +
      deriv F (u x) * fderiv ℝ (fun y => fderiv ℝ u y b) x a := by
  have hdu := hu.differentiableAt (by norm_num)
  have hF' : DifferentiableAt ℝ (deriv F) (u x) :=
    by
      simpa only [fderiv_apply_one_eq_deriv] using
        ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
          (differentiableAt_const (1 : ℝ))
  have hdu' : DifferentiableAt ℝ (fun y => fderiv ℝ u y b) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have he : (fun y => fderiv ℝ (F ∘ u) y b) =ᶠ[𝓝 x]
      (fun y => deriv F (u y) * fderiv ℝ u y b) := by
    filter_upwards [hu.eventually (by norm_num),
      (hdu.continuousAt.preimage_mem_nhds (hF.eventually (by norm_num)))] with y hy hFy
    change ContDiffAt ℝ 2 F (u y) at hFy
    exact scalar_comp_directional (hFy.differentiableAt (by norm_num))
      (hy.differentiableAt (by norm_num)) b
  rw [he.fderiv_eq]
  erw [fderiv_fun_mul (hF'.comp x hdu) hdu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  have hfder := scalar_comp_directional hF' hdu a
  change fderiv ℝ (deriv F ∘ u) x a = _ at hfder
  rw [hfder]
  simp only [Function.comp_apply]
  ring
end ScalarComposition
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
lemma localLaplacian_expansion_at {u : M → ℝ}
    (g : SmoothMetric E M) (p : M) {y : E} (hy : y ∈ (chartAt E p).target)
    (hu : ContDiffAt ℝ 2 (u ∘ (chartAt E p).symm) y) :
    localLaplacian g u p y =
      (∑ i, ∑ j, (metricCoefficients g p y)⁻¹ i j *
        fderiv ℝ (fun z => fderiv ℝ (u ∘ (chartAt E p).symm) z (Module.finBasis ℝ E j)) y
          (Module.finBasis ℝ E i)) +
      ∑ j, metricFirstCoefficient g p j y *
        fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j) := by
  classical
  let ρ := fun z => Real.sqrt (metricCoefficients g p z).det
  let A := metricCoefficients g p
  let v := u ∘ (chartAt E p).symm
  let b := Module.finBasis ℝ E
  have hρ : DifferentiableAt ℝ ρ y := ((contDiffOn_metricDensity g p).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hA (i j : CoordIndex E) : DifferentiableAt ℝ (fun z => (A z)⁻¹ i j) y :=
    ((contDiffOn_metricInverse g p i j).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hv : DifferentiableAt ℝ (fderiv ℝ v) y :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he (i : CoordIndex E) : (fun z => metricFlux g u p z i) =
      fun z => ∑ j, (ρ z * (A z)⁻¹ i j) * fderiv ℝ v z (b j) := by
    funext z
    simp only [metricFlux, ρ, A, v, b, Finset.mul_sum, mul_assoc]
  have hder (i : CoordIndex E) : fderiv ℝ (fun z => metricFlux g u p z i) y (b i) =
      ∑ j, ((ρ y * (A y)⁻¹ i j) * fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i) +
        fderiv ℝ v y (b j) * fderiv ℝ (fun z => ρ z * (A z)⁻¹ i j) y (b i)) := by
    rw [he]
    erw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j z => (ρ z * (A z)⁻¹ i j) * fderiv ℝ v z (b j))
      (fun j _ => (hρ.mul (hA i j)).mul (hv.clm_apply (differentiableAt_const _)))]
    simp only [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    erw [fderiv_mul (c := fun z => ρ z * (A z)⁻¹ i j)
      (d := fun z => fderiv ℝ v z (b j)) (hρ.mul (hA i j))
      (hv.clm_apply (differentiableAt_const _))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  change (ρ y)⁻¹ * ∑ i, fderiv ℝ (fun z => metricFlux g u p z i) y (b i) = _
  simp_rw [hder, Finset.sum_add_distrib]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  have hn : ρ y ≠ 0 := (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  have hmain : (∑ i, (ρ y)⁻¹ * ∑ j, ρ y * (A y)⁻¹ i j *
      fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i)) =
      ∑ i, ∑ j, (A y)⁻¹ i j * fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [hmain]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [metricFirstCoefficient, ρ, A, b, v, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem laplaceBeltrami_comp_at {F : ℝ → ℝ} {u : M → ℝ}
    (g : SmoothMetric E M) (x : M) (hF : ContDiffAt ℝ 2 F (u x))
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u) :
    laplaceBeltrami g (F ∘ u) x = deriv F (u x) * laplaceBeltrami g u x +
      deriv (deriv F) (u x) * coordinateGradientPair g u u x := by
  let c := chartAt E x
  let b := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hF' : ContDiffAt ℝ 2 F ((u ∘ c.symm) (c x)) := by
    simpa only [Function.comp_apply,hinv] using hF
  have hFu : ContDiffAt ℝ 2 ((F ∘ u) ∘ c.symm) (c x) := hF'.comp (c x) hu'
  change localLaplacian g (F ∘ u) x (c x) =
    deriv F (u x) * localLaplacian g u x (c x) +
      deriv (deriv F) (u x) * coordinateGradientPair g u u x
  rw [localLaplacian_expansion_at g x hx hFu, localLaplacian_expansion_C2 hu g x hx]
  have hd1 (i : CoordIndex E) :
      fderiv ℝ ((F ∘ u) ∘ c.symm) (c x) (b i) =
      deriv F (u x) * fderiv ℝ (u ∘ c.symm) (c x) (b i) := by
    change fderiv ℝ (F ∘ (u ∘ c.symm)) (c x) (b i) = _
    rw [scalar_comp_directional (hF'.differentiableAt (by norm_num))
      (hu'.differentiableAt (by norm_num)), Function.comp_apply, hinv]
  have hd2 (i j : CoordIndex E) :
      fderiv ℝ (fun z => fderiv ℝ ((F ∘ u) ∘ c.symm) z (b j)) (c x) (b i) =
      deriv (deriv F) (u x) * fderiv ℝ (u ∘ c.symm) (c x) (b i) *
        fderiv ℝ (u ∘ c.symm) (c x) (b j) +
      deriv F (u x) * fderiv ℝ (fun z => fderiv ℝ (u ∘ c.symm) z (b j)) (c x) (b i) := by
    change fderiv ℝ (fun z => fderiv ℝ (F ∘ (u ∘ c.symm)) z (b j)) (c x) (b i) = _
    rw [scalar_comp_second_directional hF' hu', Function.comp_apply,hinv]
  change (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (fun z => fderiv ℝ ((F ∘ u) ∘ c.symm) z (b j)) (c x) (b i)) +
      ∑ j, metricFirstCoefficient g x j (c x) * fderiv ℝ ((F ∘ u) ∘ c.symm) (c x) (b j) = _
  simp_rw [hd1,hd2,mul_add,Finset.sum_add_distrib]
  unfold coordinateGradientPair
  simp only [Finset.mul_sum]
  simp only [mul_left_comm,mul_comm]
  ring



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_AnnularRelativeMargin
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_PinningFactorGradient
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma laplaceBeltrami_congr_nhds (g : SmoothMetric E M) {u v : M → ℝ} {x : M}
    (hu : u =ᶠ[𝓝 x] v) : laplaceBeltrami g u x=laplaceBeltrami g v x := by
  let c := chartAt E x
  have hx := c.map_source (mem_chart_source E x)
  have ht : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv (mem_chart_source E x)] using (c.continuousAt_symm hx).tendsto
  have hu' := (hu.comp_tendsto ht).fderiv (𝕜:=ℝ)
  have he (i : CoordIndex E) :
      (fun y => Real.sqrt (metricCoefficients g x y).det * ∑ j,
        (metricCoefficients g x y)⁻¹ i j * fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))
      =ᶠ[𝓝 (c x)]
      (fun y => Real.sqrt (metricCoefficients g x y).det * ∑ j,
        (metricCoefficients g x y)⁻¹ i j * fderiv ℝ (v ∘ c.symm) y (Module.finBasis ℝ E j)) := by
    filter_upwards [hu'] with y hy
    rw [hy]
  unfold laplaceBeltrami
  change (Real.sqrt (metricCoefficients g x (c x)).det)⁻¹ * ∑ i, _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun T : E →L[ℝ] ℝ => T (Module.finBasis ℝ E i)) (he i).fderiv_eq


end



section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff

lemma pinning_factor_squared (F : ℝ → ℝ) {I : Set ℝ} (hIo : IsOpen I)
    (hIc : IsPreconnected I) (hF : ContDiffOn ℝ 2 F I)
    {n : ℕ} (hn : 2 ≤ n) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr : r₀ < r₁)
    (he : ∀ s ∈ I, ∀ r ∈ ({r₀,r₁} : Set ℝ),
      (n : ℝ)^2 * deriv (deriv F) s * (r^(n-1) - s^2) +
        ((n : ℝ)*((n : ℝ)+2)) * (F s - s * deriv F s) = 0) :
    ∃ c : ℝ, ∀ s ∈ I, F s = c * s := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : r₀^(n-1) < r₁^(n-1) := pow_lt_pow_left₀ hr hr₀.le (by omega)
  have hsecond (s : ℝ) (hs : s ∈ I) : deriv (deriv F) s = 0 := by
    have h0 := he s hs r₀ (by simp)
    have h1 := he s hs r₁ (by simp)
    have hx : (n : ℝ)^2 * (r₁^(n-1)-r₀^(n-1)) ≠ 0 :=
      (mul_pos (sq_pos_of_pos hn₀) (sub_pos.mpr hp)).ne'
    have hz : ((n : ℝ)^2 * (r₁^(n-1)-r₀^(n-1))) * deriv (deriv F) s = 0 := by
      nlinarith [h0,h1]
    exact (mul_eq_zero.mp hz).resolve_left hx
  have hd : DifferentiableOn ℝ (deriv F) I :=
    (hF.deriv_of_isOpen (m := 1) hIo (by norm_num)).differentiableOn (by norm_num)
  obtain ⟨c,hc⟩ := hIo.exists_is_const_of_deriv_eq_zero hIc hd (fun s hs => hsecond s hs)
  refine ⟨c,fun s hs => ?_⟩
  have h0 := he s hs r₀ (by simp)
  rw [hsecond s hs,hc s hs] at h0
  have hlambda : (n : ℝ)*((n : ℝ)+2) ≠ 0 := (mul_pos hn₀ (by linarith)).ne'
  have hz : F s - s * c = 0 := (mul_eq_zero.mp (by simpa using h0)).resolve_left hlambda
  linarith
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma chart_germ_of_pullback {u v : M → ℝ} (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target)
    (he : (u ∘ (chartAt E p).symm) =ᶠ[𝓝 y] (v ∘ (chartAt E p).symm)) :
    u =ᶠ[𝓝 ((chartAt E p).symm y)] v := by
  let c := chartAt E p
  have hs : c.symm y ∈ c.source := c.map_target hy
  have ht : Tendsto c (𝓝 (c.symm y)) (𝓝 y) := by
    simpa only [c.right_inv hy] using (c.continuousAt hs).tendsto
  filter_upwards [he.comp_tendsto ht,c.open_source.mem_nhds hs] with z hz hzs
  change u (c.symm (c z)) = v (c.symm (c z)) at hz
  simpa only [c.left_inv hzs] using hz

theorem local_eigen_proportional_of_annular_rank
    (g : SmoothMetric E M) {u v R : M → ℝ} (p : M) {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hUt : U ⊆ (chartAt E p).target)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 v)
    (hdu : fderiv ℝ (u ∘ (chartAt E p).symm) x ≠ 0)
    (hker : ∀ y ∈ U, ∀ w, fderiv ℝ (u ∘ (chartAt E p).symm) y w = 0 →
      fderiv ℝ (v ∘ (chartAt E p).symm) y w = 0)
    (hpair : ContDiffAt ℝ 1 (fun y => (u ((chartAt E p).symm y), R ((chartAt E p).symm y))) x)
    (hrank : Function.Surjective (fderiv ℝ
      (fun y => (u ((chartAt E p).symm y), R ((chartAt E p).symm y))) x))
    (hR : 0 < R ((chartAt E p).symm x)) {n : ℕ} (hn : 2 ≤ n)
    (hue : ∀ y ∈ U, laplaceBeltrami g u ((chartAt E p).symm y) =
      -((n:ℝ)*((n:ℝ)+2)) * u ((chartAt E p).symm y))
    (hve : ∀ y ∈ U, laplaceBeltrami g v ((chartAt E p).symm y) =
      -((n:ℝ)*((n:ℝ)+2)) * v ((chartAt E p).symm y))
    (hquad : ∀ y ∈ U, coordinateGradientPair g u u ((chartAt E p).symm y) =
      (n:ℝ)^2 * ((R ((chartAt E p).symm y))^(n-1) - (u ((chartAt E p).symm y))^2)) :
    ∃ c : ℝ, v =ᶠ[𝓝 ((chartAt E p).symm x)] (fun y => c*u y) := by
  let chart := chartAt E p
  let f := u ∘ chart.symm
  let h := v ∘ chart.symm
  let H : E → ℝ × ℝ := fun y => (f y, R (chart.symm y))
  have hf : ContDiffOn ℝ 2 f U := fun y hy =>
    (contDiffAt_inChart_C2 hu p (hUt hy)).contDiffWithinAt
  have hh : ContDiffOn ℝ 2 h U := fun y hy =>
    (contDiffAt_inChart_C2 hv p (hUt hy)).contDiffWithinAt
  obtain ⟨V,I,F,hVo,hxV,hVU,hIo,hIc,hfxI,hF,hfV,hVF⟩ :=
    local_factor_of_kernel hU hx hf hh hdu hker
  have hlocal (y : E) (hy : y ∈ V) :
      v =ᶠ[𝓝 (chart.symm y)] (F ∘ u) := by
    apply chart_germ_of_pullback p (hUt (hVU hy))
    filter_upwards [hVo.mem_nhds hy] with z hz
    exact hVF hz
  have hPDE (y : E) (hy : y ∈ V) :
      (n:ℝ)^2 * deriv (deriv F) (f y) * ((R (chart.symm y))^(n-1) - (f y)^2) +
      ((n:ℝ)*((n:ℝ)+2)) * (F (f y) - f y * deriv F (f y)) = 0 := by
    have hcomp := laplaceBeltrami_comp_at g (chart.symm y)
      ((hF _ (hfV hy)).contDiffAt (hIo.mem_nhds (hfV hy))) hu
    rw [← laplaceBeltrami_congr_nhds g (hlocal y hy),hue y (hVU hy),hve y (hVU hy),hquad y (hVU hy)] at hcomp
    have hval : v (chart.symm y) = F (f y) := hVF hy
    rw [hval] at hcomp
    change -((n:ℝ)*((n:ℝ)+2))*F (f y) =
      deriv F (f y) * (-((n:ℝ)*((n:ℝ)+2))*f y) +
      deriv (deriv F) (f y) * ((n:ℝ)^2 * ((R (chart.symm y))^(n-1) - (f y)^2)) at hcomp
    linear_combination -hcomp
  have hmap : Filter.map H (𝓝 x) = 𝓝 (H x) :=
    (hpair.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hrank)
  have himage : H '' V ∈ 𝓝 (H x) := by
    rw [←hmap]
    exact Filter.image_mem_map (hVo.mem_nhds hxV)
  have hbox : I ×ˢ Ioi (0:ℝ) ∈ 𝓝 (H x) :=
    (hIo.prod isOpen_Ioi).mem_nhds ⟨hfxI,hR⟩
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp (inter_mem himage hbox)
  let K := ball (f x) ε
  let r₀ := R (chart.symm x) - ε/2
  let r₁ := R (chart.symm x) + ε/2
  have hr₀B : r₀ ∈ ball (R (chart.symm x)) ε := by
    rw [mem_ball,Real.dist_eq,abs_lt]; dsimp [r₀]; constructor <;> linarith
  have hr₁B : r₁ ∈ ball (R (chart.symm x)) ε := by
    rw [mem_ball,Real.dist_eq,abs_lt]; dsimp [r₁]; constructor <;> linarith
  have hpairmem (s : ℝ) (hs : s ∈ K) (r : ℝ) (hr : r ∈ ({r₀,r₁}:Set ℝ)) :
      (s,r) ∈ H '' V ∩ (I ×ˢ Ioi (0:ℝ)) := by
    apply hεsub
    change (s,r) ∈ ball (f x,R (chart.symm x)) ε
    rw [←ball_prod_same]
    refine ⟨hs,?_⟩
    simp only [mem_insert_iff,mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> assumption
  have hKI : K ⊆ I := fun s hs => (hpairmem s hs r₀ (by simp)).2.1
  have hr₀pos : 0 < r₀ := (hpairmem (f x) (mem_ball_self hε) r₀ (by simp)).2.2
  have hrr : r₀ < r₁ := by dsimp [r₀,r₁]; linarith
  obtain ⟨a,ha⟩ := pinning_factor_squared F isOpen_ball (convex_ball (f x) ε).isPreconnected
    (hF.mono hKI) hn hr₀pos hrr (fun s hs r hr => by
      obtain ⟨y,hy,hyr⟩ := (hpairmem s hs r hr).1
      have hs' : f y = s := congrArg Prod.fst hyr
      have hr' : R (chart.symm y) = r := congrArg Prod.snd hyr
      simpa only [hs',hr'] using hPDE y hy)
  refine ⟨a,chart_germ_of_pullback p (hUt hx) ?_⟩
  have hnx : f ⁻¹' K ∈ 𝓝 x :=
    ((hf x hx).contDiffAt (hU.mem_nhds hx)).continuousAt (isOpen_ball.mem_nhds (mem_ball_self hε))
  filter_upwards [hVo.mem_nhds hxV,hnx] with y hy hyK
  exact (hVF hy).trans (ha (f y) hyK)


end

open Set Filter Function Manifold Metric
open scoped Topology ContDiff

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

open Set Filter Function Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma transverse_zero_kernel (g : SmoothMetric E M) (u v : M → ℝ) (x : M)
    (hp : bundleTransverse g u x (metricGradient g v x) = 0)
    (w : TangentSpace 𝓘(ℝ,E) x) (hw : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u x w = 0) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) v x w = 0 := by
  have hv : metricGradient g v x =
      (g.inner x (metricGradient g u x) (metricGradient g u x))⁻¹ •
        (g.inner x (metricGradient g u x) (metricGradient g v x) • metricGradient g u x) := by
    simpa only [bundleTransverse,sub_apply,ContinuousLinearMap.id_apply,
      smul_apply,bundleRankOne,ContinuousLinearMap.smulRight_apply,
      sub_eq_zero] using hp
  have hzero : g.inner x (metricGradient g u x) w = 0 :=
    (metricGradient_pairing g u x w).trans hw
  rw [←metricGradient_pairing g v x w,hv]
  erw [map_smul, smul_apply, map_smul, smul_apply, hzero]
  simp only [smul_zero]
  rfl
lemma transverse_zero_chart_kernel (g : SmoothMetric E M) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target)
    (hp : bundleTransverse g u ((chartAt E p).symm y)
      (metricGradient g v ((chartAt E p).symm y)) = 0) :
    ∀ w, fderiv ℝ (u ∘ (chartAt E p).symm) y w = 0 →
      fderiv ℝ (v ∘ (chartAt E p).symm) y w = 0 := by
  intro w hw
  have hd := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) p) hy).mdifferentiableAt (by simp)
  have he (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f) :
      fderiv ℝ (f ∘ (chartAt E p).symm) y w =
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f ((chartAt E p).symm y)
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y w) := by
    have hh := mfderiv_comp y (hf.mdifferentiable (by simp)).mdifferentiableAt hd
    rw [mfderiv_eq_fderiv] at hh
    exact congrArg (fun L => L w) hh
  rw [he u hu] at hw
  rw [he v hv]
  exact transverse_zero_kernel g u v _ hp _ hw



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateGradientPairCongrNhds
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
lemma exists_annular_rank_point (a b c : Euclidean (d+1))
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hc : inner ℝ c c = 1)
    (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (n : ℕ) (hn : 0 < n) {l h : ℝ} (hl : 0 < l) (hlh : l < h) (hh : h < 1) :
    ∃ p : Sphere d, l < Complex.normSq (planarLinear a b p) ∧
      Complex.normSq (planarLinear a b p) < h ∧ ((planarLinear a b p)^n).im ≠ 0 := by
  let s := (l+h)/2
  have hs : 0 < s := by dsimp [s]; linarith
  obtain ⟨z,hzr,hzn⟩ := exists_power_radius n hn (Real.sqrt_pos.mpr hs)
  have hz : Complex.normSq z = s := by rwa [Real.sq_sqrt hs.le] at hzr
  obtain ⟨p,hp,hpz⟩ := planar_sphere_point a b c ha hb hc hab hac hbc z
    (by rw [hz]; dsimp [s]; linarith)
  let q : Sphere d := ⟨p,by simpa only [Metric.mem_sphere,dist_zero_right] using hp⟩
  refine ⟨q,?_,?_,?_⟩
  · change l < Complex.normSq (planarLinear a b p)
    rw [hpz,hz]; dsimp [s]; linarith
  · change Complex.normSq (planarLinear a b p) < h
    rw [hpz,hz]; dsimp [s]; linarith
  · change ((planarLinear a b p)^n).im ≠ 0
    rwa [hpz]
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
section LocalPair
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma coordinateGradientPair_congr_nhds (g : SmoothMetric E M) {u v : M → ℝ} {x : M}
    (he : u =ᶠ[𝓝 x] v) : coordinateGradientPair g u u x = coordinateGradientPair g v v x := by
  let c := chartAt E x
  have hx : c x ∈ c.target := c.map_source (mem_chart_source _ _)
  have ht : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv (mem_chart_source _ _)] using (c.continuousAt_symm hx).tendsto
  have hd : fderiv ℝ (u ∘ c.symm) (c x) = fderiv ℝ (v ∘ c.symm) (c x) :=
    (he.comp_tendsto ht).fderiv_eq
  dsimp only [c] at hd
  simp only [coordinateGradientPair,hd]
end LocalPair
variable {d : ℕ}

theorem annular_transverse_zero_proportional [PreconnectedSpace (Sphere d)]
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
    (hzero : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h → bundleTransverse g u p (metricGradient g v p) = 0) :
    ∃ t : ℝ, v = fun p => t*u p := by
  let A := {p : Sphere d | l < Complex.normSq (planarLinear a b p) ∧
    Complex.normSq (planarLinear a b p) < h}
  have hAo : IsOpen A := round_annulus_open a b l h
  obtain ⟨p,hpl,hph,hpn⟩ := exists_annular_rank_point a b c ha hb hc hab hac hbc n (by omega) hl hlh hh
  let chart := chartAt (Euclidean d) p
  have hsym : chart.symm 0 = p := by
    change (chartAt (Euclidean d) p).symm 0 = p
    simpa only [sphere_chart_center] using (chartAt (Euclidean d) p).left_inv (mem_chart_source _ p)
  let U := chart.symm ⁻¹' A
  have hU : IsOpen U := hAo.preimage (sphere_chart_symm_continuous_general p)
  have hx : (0 : Euclidean d) ∈ U := by change chart.symm 0 ∈ A; rw [hsym]; exact ⟨hpl,hph⟩
  have hUt : U ⊆ chart.target := by rw [sphere_chart_target]; exact subset_univ _
  have hgerm (q : Sphere d) (hq : q ∈ A) : u =ᶠ[𝓝 q] roundPower a b n := by
    filter_upwards [hAo.mem_nhds hq] with z hz
    exact hup z hz.1 hz.2
  have hchart : (u ∘ chart.symm) =ᶠ[𝓝 (0 : Euclidean d)] (roundPower a b n ∘ chart.symm) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hup _ hy.1 hy.2
  let R := fun q : Sphere d => Complex.normSq (planarLinear a b q)
  let H := fun y : Euclidean d => (u (chart.symm y),R (chart.symm y))
  have hH : H =ᶠ[𝓝 0] (roundPowerRadius a b n ∘ chart.symm) := by
    filter_upwards [hchart] with y hy
    change (u (chart.symm y),R (chart.symm y)) =
      (((planarLinear a b (chart.symm y))^n).re,Complex.normSq (planarLinear a b (chart.symm y)))
    exact Prod.ext hy rfl
  have hdu : fderiv ℝ (u ∘ chart.symm) 0 ≠ 0 := by
    rw [hchart.fderiv_eq]
    exact roundPower_annulus_noncritical a b n (by omega) ha hb hab p (hl.trans hpl) (hph.trans hh)
  have hquad (y : Euclidean d) (hy : y ∈ U) :
      coordinateGradientPair g u u (chart.symm y) =
        (n:ℝ)^2 * ((R (chart.symm y))^(n-1) - (u (chart.symm y))^2) := by
    rw [coordinateGradientPair_congr_nhds g (hgerm _ hy),
      roundPower_coordinateGradientPair g _ (hgp _ hy.1 hy.2) a b n (by omega) ha hb hab,
      hup _ hy.1 hy.2]
  have hpr : ContDiffAt ℝ 1 H 0 ∧ Function.Surjective (fderiv ℝ H 0) :=
    round_pair_rank_transfer a b n (by omega) p ha hb hab (hph.trans hh) hpn hH
  obtain ⟨t,ht⟩ := local_eigen_proportional_of_annular_rank g (u := u) (v := v) (R := R) p (U := U) (x := 0) hU hx hUt
    (hu.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) (hv.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hdu
    (fun y hy => transverse_zero_chart_kernel g hu hv p (hUt hy) (hzero _ hy.1 hy.2))
    hpr.1 hpr.2
    (by change 0 < R (chart.symm 0); rw [hsym]; exact hl.trans hpl) hn
    (fun y _ => by linarith [hue (chart.symm y)])
    (fun y _ => by linarith [hve (chart.symm y)]) hquad
  exact ⟨t,proportional_eigen_global g hu hv _ t hue hve ⟨chart.symm 0,ht⟩⟩



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_AnnularOrthogonalTransverseNonzero
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
section Orthogonality
variable {M : Type*} [TopologicalSpace M] [CompactSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M]
lemma proportional_orthogonal_zero (μ : Measure M) [Measure.IsOpenPosMeasure μ]
    [IsFiniteMeasureOnCompacts μ] {u v : M → ℝ} (hv : Continuous v)
    (ht : ∃ t : ℝ, v = fun x => t*u x) (ho : ∫ x, v x*u x ∂μ = 0) : v = 0 := by
  by_contra hn
  obtain ⟨x,hx⟩ : ∃ x, v x ≠ 0 := by
    by_contra hn'; push Not at hn'; exact hn (funext hn')
  have hp : 0 < ∫ x, v x*v x ∂μ :=
    (hv.mul hv).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun x => mul_self_nonneg (v x))
      (mul_self_pos.mpr hx).ne'
  obtain ⟨t,ht⟩ := ht
  have he : (fun x => v x*v x) = fun x => t*(v x*u x) := by
    funext x
    rw [congrFun ht x]
    ring
  rw [he, integral_const_mul, ho, mul_zero] at hp
  exact (lt_irrefl 0) hp
end Orthogonality

end

open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}
theorem annular_orthogonal_transverse_nonzero_oai [PreconnectedSpace (Sphere d)]
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
    (hv0 : v ≠ 0) (ho : ∫ q, v q*u q ∂μ = 0) :
    ∃ p : Sphere d, l < Complex.normSq (planarLinear a b p) ∧
      Complex.normSq (planarLinear a b p) < h ∧
      bundleTransverse g u p (metricGradient g v p) ≠ 0 := by
  classical
  by_contra hnone
  apply hv0
  apply proportional_orthogonal_zero μ hv.continuous _ ho
  apply annular_transverse_zero_proportional g a b c ha hb hc hab hac hbc n hn hl hlh hh hu hv hue hve hup hgp
  intro p hpl hph
  by_contra hz
  exact hnone ⟨p,hpl,hph,hz⟩




end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.annular_orthogonal_transverse_nonzero_oai := @OAI.YauCounterexamples.annular_orthogonal_transverse_nonzero_oai
