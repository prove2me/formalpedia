-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_integral_line_gram_cd685deb188c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:42.841531+00:00
-- url     : https://prove2.me/submissions/566c175d-6ec4-40fc-903f-cacc44672021

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeChartGram
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_indicator_ball_norm_pow_269848d30fd3


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
open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (e : ℕ) (h : HermNorm n) (g : (Fin n → ℂ) → ℝ)
    (hg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x) (x : Fin n → ℂ) (hx : x ≠ 0) (G : ℝ) :
    ∫ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => g (h.pointOf z))
          (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G) =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
        (g x * ((e.factorial : ℝ) / Real.pi ^ e * G / h.dualNorm x ^ (2 * (e + 1)))) := by
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  have hinv : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hMx : (h.matᵀ)⁻¹ *ᵥ x ≠ 0 := by
    intro h0
    apply hx
    rw [← hinv, h0, Matrix.mulVec_zero]
  set ρ := ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ with hρ_def
  have hρx : h.dualNorm x = ρ := by
    rw [hρ_def, EuclideanSpace.norm_eq]
    rfl
  have hρ : 0 < ρ := by
    rw [hρ_def, norm_pos_iff]
    intro h0
    exact hMx (by simpa using congrArg WithLp.ofLp h0)
  have hpt : ∀ t : ℂ, h.pointOf (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = t • x := by
    intro t
    have : (fun i => (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) i) = t • ((h.matᵀ)⁻¹ *ᵥ x) := by
      ext i
      simp
    simp only [HermNorm.pointOf, this, Matrix.mulVec_smul, hinv]
  have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => g (h.pointOf z)) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) =ᵐ[volume]
      fun t => (g x * G) * (ball (0 : ℂ) (1 / ρ)).indicator (fun t => ‖t‖ ^ (2 * e)) t := by
    have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with t ht
    have hiff : ‖t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ < 1 ↔ ‖t‖ < 1 / ρ := by
      rw [norm_smul, lt_div_iff₀ hρ]
    by_cases hb : ‖t‖ < 1 / ρ
    · rw [indicator_of_mem (mem_ball_zero_iff.2 (hiff.2 hb)),
        indicator_of_mem (mem_ball_zero_iff.2 hb), hpt, hg t x ht]
      ring
    · rw [indicator_of_notMem (fun h => hb (hiff.1 (mem_ball_zero_iff.1 h))),
        indicator_of_notMem (fun h => hb (mem_ball_zero_iff.1 h))]
      ring
  rw [integral_congr_ae hae, integral_const_mul,
    integral_indicator_ball_norm_pow e (by positivity), hρx]
  rw [one_div, inv_pow, Nat.factorial_succ]
  have hρ' : ρ ^ (2 * (e + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
end GroundTheory.Heights₂.Heights
