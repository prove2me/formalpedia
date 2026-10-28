-- Prove2me | solution 1 for OAI.YauCounterexamples.round_pair_rank_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:43:23.085004+00:00
-- url     : https://prove2.me/submissions/7e9a980d-934f-49b7-b85d-747a7bdccb04

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

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

attribute [local instance] OAI.YauCounterexamples.instFactEqNatFinrankRealEuclideanHAddOfNat_1
lemma sphereFrame_coordinates (p : Sphere n) (a : Euclidean (n+1)) :
    sphereFrame p (sphereCoordinates p a) = sphereProjection p a := by
  change (((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm
      ((OrthonormalBasis.fromOrthogonalSpanSingleton n
        (ne_zero_of_mem_unit_sphere (-p))).repr ⟨sphereProjection p a,_⟩)) : Euclidean (n+1)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PlanarTangentSurjective
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
section Plane
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem planar_tangent_surjective (a b p : E)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (hp : inner ℝ p p = 1) (hR : Complex.normSq (planarLinear a b p) < 1) :
    ∀ z : ℂ, ∃ v : E, inner ℝ p v = 0 ∧ planarLinear a b v = z := by
  intro z
  have hba : inner ℝ b a = 0 := (real_inner_comm a b).trans hab
  let A := inner ℝ a p
  let B := inner ℝ b p
  let R := A*A+B*B
  have hR' : R < 1 := by
    simpa [R,A,B,planarLinear_apply,Complex.normSq_apply] using hR
  have hden : 1-R ≠ 0 := (sub_pos.mpr hR').ne'
  let q := p - (A • a + B • b)
  let w := z.re • a + z.im • b
  have hqa : inner ℝ a q = 0 := by simp only [q,A,B,inner_sub_right,inner_add_right,inner_smul_right,ha,hab,mul_one,mul_zero,add_zero,sub_self]
  have hqb : inner ℝ b q = 0 := by simp only [q,A,B,inner_sub_right,inner_add_right,inner_smul_right,hb,hba,mul_one,mul_zero,zero_add,sub_self]
  have hqp : inner ℝ p q = 1-R := by
    simp only [q,inner_sub_right,inner_add_right,inner_smul_right,hp]
    rw [real_inner_comm a p,real_inner_comm b p]
  have hqz : planarLinear a b q = 0 := by simp [planarLinear_apply,hqa,hqb]
  have hw : planarLinear a b w = z := by
    simp only [planarLinear_apply,w,inner_add_right,inner_smul_right,ha,hb,hab,hba,
      mul_one,mul_zero,add_zero,zero_add]
    simpa only [mul_comm Complex.I] using Complex.re_add_im z
  refine ⟨w - (inner ℝ p w / (1-R)) • q, ?_, ?_⟩
  · rw [inner_sub_right,inner_smul_right,hqp,div_mul_cancel₀ _ hden,sub_self]
  · rw [map_sub,map_smul,hqz,smul_zero,sub_zero,hw]
end Plane
variable {d : ℕ}
lemma planar_sphereFrame_surjective (a b : Euclidean (d+1)) (p : Sphere d)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (hR : Complex.normSq (planarLinear a b (p : Euclidean (d+1))) < 1) :
    Function.Surjective ((planarLinear a b).comp (sphereFrame p).toContinuousLinearMap) := by
  intro z
  have hp : inner ℝ (p : Euclidean (d+1)) (p : Euclidean (d+1)) = 1 := by
    rw [real_inner_self_eq_norm_sq]
    simp
  obtain ⟨v,hpv,hv⟩ := planar_tangent_surjective a b (p : Euclidean (d+1)) ha hb hab hp hR z
  refine ⟨sphereCoordinates p v,?_⟩
  change planarLinear a b (sphereFrame p (sphereCoordinates p v)) = z
  rw [sphereFrame_coordinates]
  simpa only [sphereProjection,hpv,zero_smul,sub_zero] using hv
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_RoundPowerRadius
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
open Set Filter
open scoped Topology ContDiff ComplexConjugate

lemma powerRadiusMap_contDiff (n : ℕ) : ContDiff ℝ ∞ (powerRadiusMap n) := by
  unfold powerRadiusMap
  apply ContDiff.prodMk
  · exact Complex.reCLM.contDiff.comp (contDiff_id.pow n)
  · change ContDiff ℝ ∞ (fun z : ℂ => z.re*z.re + z.im*z.im)
    exact
      (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
        (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
lemma powerRadiusMap_directional (n : ℕ) (z v : ℂ) :
    fderiv ℝ (powerRadiusMap n) z v =
      (((n:ℂ)*z^(n-1)*v).re, 2*(z.re*v.re + z.im*v.im)) := by
  have hp : HasFDerivAt (fun w : ℂ => w^n)
      (((n:ℂ)*z^(n-1)) • (ContinuousLinearMap.id ℝ ℂ)) z := by
    simpa using ((hasFDerivAt_id z).pow n)
  have hr := Complex.reCLM.hasFDerivAt.comp z hp
  have hn : HasFDerivAt (fun w : ℂ => Complex.normSq w)
      (2 • ((z.re • Complex.reCLM) + (z.im • Complex.imCLM))) z := by
    have h := ((Complex.reCLM.hasFDerivAt (x:=z)).mul Complex.reCLM.hasFDerivAt).add
      (Complex.imCLM.hasFDerivAt.mul Complex.imCLM.hasFDerivAt)
    have he : 2 • ((z.re • Complex.reCLM) + (z.im • Complex.imCLM)) =
        z.re • Complex.reCLM + z.re • Complex.reCLM +
          (z.im • Complex.imCLM + z.im • Complex.imCLM) := by
      ext w
      simp only [smul_apply, add_apply, smul_eq_mul,
        Complex.reCLM_apply,Complex.imCLM_apply]
      ring
    rw [he]
    exact h
  have h : HasFDerivAt (fun w : ℂ => ((w^n).re,Complex.normSq w))
      ((Complex.reCLM.comp (((n:ℂ)*z^(n-1)) • ContinuousLinearMap.id ℝ ℂ)).prod
        (2 • ((z.re • Complex.reCLM) + (z.im • Complex.imCLM)))) z :=
    hr.prodMk hn
  change fderiv ℝ (fun w : ℂ => ((w^n).re,Complex.normSq w)) z v = _
  rw [h.fderiv]
  simp [ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,smul_eq_mul]
  ring

theorem powerRadiusMap_surjective (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : (z^n).im ≠ 0) :
    Function.Surjective (fderiv ℝ (powerRadiusMap n) z) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hz0 : z ≠ 0 := by
    intro he
    simp only [he,zero_pow (show n ≠ 0 by omega),Complex.zero_im] at hz
    exact hz rfl
  have hR : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz0).ne'
  have hrad : fderiv ℝ (powerRadiusMap n) z z =
      ((n:ℝ)*(z^n).re,2*Complex.normSq z) := by
    rw [powerRadiusMap_directional]
    have he : (n:ℂ)*z^(n-1)*z = (n:ℂ)*z^n := by rw [mul_assoc,← pow_succ,Nat.sub_add_cancel hn]
    rw [he]
    simp [Complex.mul_re,Complex.normSq_apply]
  have hang : fderiv ℝ (powerRadiusMap n) z (Complex.I*z) =
      (-(n:ℝ)*(z^n).im,0) := by
    rw [powerRadiusMap_directional]
    have he : (n:ℂ)*z^(n-1)*(Complex.I*z) = Complex.I*((n:ℂ)*z^n) := by
      rw [show z^n = z^(n-1)*z by rw [← pow_succ,Nat.sub_add_cancel hn]]
      ring
    rw [he]
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.natCast_re,Complex.natCast_im,zero_mul,add_zero,zero_add,
      one_mul,sub_zero,zero_sub]
    congr 1 <;> ring
  rintro ⟨s,t⟩
  let β : ℝ := t/(2*Complex.normSq z)
  let α : ℝ := (β*(n:ℝ)*(z^n).re-s)/((n:ℝ)*(z^n).im)
  refine ⟨β • z + α • (Complex.I*z),?_⟩
  rw [map_add,map_smul,map_smul,hrad,hang]
  ext <;> dsimp [α,β] <;> field_simp [hn0,hz,hR] <;> ring

end

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter
open scoped Topology ContDiff ComplexConjugate
variable {d : ℕ}
lemma roundPowerRadius_chart (a b : Euclidean (d+1)) (k : ℕ) (p : Sphere d) :
    roundPowerRadius a b k ∘ (chartAt (Euclidean d) p).symm =
      powerRadiusMap k ∘ planarLinear a b ∘ roundChart (p : Euclidean (d+1)) (sphereFrame p) := by
  funext y
  change powerRadiusMap k (planarLinear a b ((chartAt (Euclidean d) p).symm y : Euclidean (d+1))) = _
  exact congrArg (fun z => powerRadiusMap k (planarLinear a b z)) (congrFun (sphere_chart_symm p) y)
lemma roundPowerRadius_chart_contDiff (a b : Euclidean (d+1)) (k : ℕ) (p : Sphere d) :
    ContDiff ℝ ∞ (roundPowerRadius a b k ∘ (chartAt (Euclidean d) p).symm) := by
  rw [roundPowerRadius_chart]
  exact (powerRadiusMap_contDiff k).comp ((planarLinear a b).contDiff.comp (roundChart_smooth _ _))

theorem roundPowerRadius_chart_surjective (a b : Euclidean (d+1)) (k : ℕ) (p : Sphere d)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (hk : 1 ≤ k) (hR : Complex.normSq (planarLinear a b (p : Euclidean (d+1))) < 1)
    (htheta : ((planarLinear a b (p : Euclidean (d+1)))^k).im ≠ 0) :
    Function.Surjective (fderiv ℝ (roundPowerRadius a b k ∘ (chartAt (Euclidean d) p).symm) 0) := by
  rw [roundPowerRadius_chart]
  rw [fderiv_comp 0 ((powerRadiusMap_contDiff k).differentiable (by simp) _)
    ((planarLinear a b).differentiableAt.comp 0 ((roundChart_smooth _ _).differentiable (by simp) _))]
  rw [fderiv_comp 0 (planarLinear a b).differentiableAt ((roundChart_smooth _ _).differentiable (by simp) _)]
  rw [ContinuousLinearMap.fderiv, (roundChart_first _ _).fderiv, Function.comp_apply,roundChart_zero]
  exact (powerRadiusMap_surjective k hk _ htheta).comp (planar_sphereFrame_surjective a b p ha hb hab hR)



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
lemma round_pair_rank_transfer_oai (a b : Euclidean (d+1)) (n : ℕ) (hn : 1 ≤ n)
    (p : Sphere d) (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (hr : Complex.normSq (planarLinear a b p) < 1)
    (hi : ((planarLinear a b p)^n).im ≠ 0) {H : Euclidean d → ℝ × ℝ}
    (he : H =ᶠ[𝓝 0] (roundPowerRadius a b n ∘ (chartAt (Euclidean d) p).symm)) :
    ContDiffAt ℝ 1 H 0 ∧ Function.Surjective (fderiv ℝ H 0) := by
  constructor
  · exact (((roundPowerRadius_chart_contDiff a b n p).of_le
      (show (1 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top))).contDiffAt.congr_of_eventuallyEq he)
  · rw [he.fderiv_eq]
    exact roundPowerRadius_chart_surjective a b n p ha hb hab hn hr hi


end

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace



end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.round_pair_rank_transfer_oai := @OAI.YauCounterexamples.round_pair_rank_transfer_oai
