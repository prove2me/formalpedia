-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionInjectivity_proof_6840946bc339
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:53.050826+00:00
-- url     : https://prove2.me/submissions/ee3c994d-d255-43e8-8f85-33d0a77c268e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroMore
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionInjectivity_isLive_of_mem_points_9bcc7614fe08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionInjectivity_evalCone_chartMonomial_ne_zero_af6a06a6bc14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionInjectivity_chartForm_cross_7af2443d38e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionInjectivity_chartForm_mul_pow_64b836c95b94
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionInjectivity_deg_eq_b9c28d0b278f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionInjectivity_metric_eq_bad708170f1e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open SectionInjectivity
namespace GroundTheory.Heights₂.Heights
namespace SectionInjectivity
theorem _root_.solution : SectionInjectivity.Statement := by
  intro ι _ _ n P M k q hkq e C he0 heC t
  refine ⟨fun s hs ↦ ?_, fun s₁ s₂ h ↦ mul_right_cancel₀ (pow_ne_zero t he0) h⟩
  refine ⟨IntegralSection.cast (deg_eq M hkq t) (s.mul (e.pow t)), ?_, ?_⟩
  · simp only [IntegralSection.toFun, IntegralSection.cast, IntegralSection.mul, IntegralSection.pow,
      map_mul, map_pow]
    rw [div_pow, mul_div_mul_comm]
  · intro z hz c d f hcf hzc
    have hlive := isLive_of_mem_points hz hzc
    obtain ⟨d₁, f₁, hcf₁⟩ := s.regular c hlive
    obtain ⟨d₂, f₂, hcf₂⟩ := e.regular c hlive
    have hs₁ := hs z hz c d₁ f₁ hcf₁ hzc
    have he₂ := heC z hz c d₂ f₂ hcf₂ hzc
    have hf : s.den * e.den ^ t * f - s.num * e.num ^ t * chartMonomial c d ∈ P.ideal := hcf.2
    have hprod := chartForm_mul_pow t hcf₁.2 hcf₂.2
    have hden : s.den * e.den ^ t ∉ P.ideal :=
      (IntegralSection.cast (deg_eq M hkq t) (s.mul (e.pow t))).den_not_mem
    have hev := hz.2 _ (chartForm_cross hden hf hprod)
    have hμ := evalCone_chartMonomial_ne_zero hzc d
    have hμ₁ := evalCone_chartMonomial_ne_zero hzc d₁
    have hμ₂ := evalCone_chartMonomial_ne_zero hzc d₂
    rw [chartMonomial_add, chartMonomial_nsmul] at hev
    simp only [evalCone, eval₂_sub, eval₂_mul, eval₂_pow] at hev hμ hμ₁ hμ₂ hs₁ he₂ ⊢
    rw [metric_eq M hkq t hz.1, Real.exp_zero]
    have hN := ((((M.pow (q - k)).mul (HermLine.standard n)).pow t).metric_pos z hz.1)
    have hE := (((M.pow k).mul (HermLine.standard n).inv).metric_pos z hz.1)
    set x := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) f
    set x₁ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) f₁
    set x₂ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) f₂
    set μ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) (chartMonomial c d)
    set μ₁ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) (chartMonomial c d₁)
    set μ₂ := eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) (chartMonomial c d₂)
    set hNz := (((M.pow (q - k)).mul (HermLine.standard n)).pow t).metric z
    set hEz := ((M.pow k).mul (HermLine.standard n).inv).metric z
    have hnorm : ‖x‖ * (‖μ₁‖ * ‖μ₂‖ ^ t) = ‖x₁‖ * ‖x₂‖ ^ t * ‖μ‖ := by
      have h := congrArg norm (sub_eq_zero.mp hev)
      simpa only [norm_mul, norm_pow] using h
    have hμ' := norm_pos_iff.mpr hμ
    have hμ₁' := norm_pos_iff.mpr hμ₁
    have hμ₂' := norm_pos_iff.mpr hμ₂
    have key : ‖x‖ / (‖μ‖ * (hNz * hEz ^ t)) = ‖x₁‖ / (‖μ₁‖ * hNz) * (‖x₂‖ / (‖μ₂‖ * hEz)) ^ t := by
      rw [div_pow, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
      linear_combination (hNz * hEz ^ t) * hnorm
    rw [key]
    calc ‖x₁‖ / (‖μ₁‖ * hNz) * (‖x₂‖ / (‖μ₂‖ * hEz)) ^ t
        ≤ Real.exp (-(t * C)) * Real.exp C ^ t :=
          mul_le_mul hs₁ (pow_le_pow_left₀ (by positivity) he₂ t) (by positivity) (by positivity)
      _ = 1 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; simp
end SectionInjectivity
end GroundTheory.Heights₂.Heights
