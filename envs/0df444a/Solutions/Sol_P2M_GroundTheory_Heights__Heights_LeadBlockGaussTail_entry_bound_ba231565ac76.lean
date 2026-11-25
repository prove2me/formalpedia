-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_entry_bound_ba231565ac76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:32.210595+00:00
-- url     : https://prove2.me/submissions/5aa3c70a-85e9-4e56-b81d-ab5d7fc99836

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_halfGauss_lt_top_d8f4b704046d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_ballInd_le_one_716bc4ee4da8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_exp_mul_pow_le_44018617e26c

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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail
namespace GroundTheory.Heights₂.Heights.LeadBlockGaussTail
theorem _root_.solution (ρ : ℝ) (p : ℕ) (hp : p ≤ 1) :
    ∫⁻ z : ℂ, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) * ENNReal.ofReal ((‖z‖ ^ 2) ^ p) * ballInd ρ z ≤
      ENNReal.ofReal (entryConst / (1 + ρ ^ 2) ^ (p + 1)) := by
  have hG := halfGauss_lt_top
  have hG0 : 0 ≤ halfGauss.toReal := ENNReal.toReal_nonneg
  have hpi := Real.pi_pos
  have hq : 0 < (1 + ρ ^ 2) ^ (p + 1) := by positivity
  have h24 : (2 : ℝ) ^ (p + 1) ≤ 4 := by interval_cases p <;> norm_num
  rcases le_or_gt (ρ ^ 2) 1 with hρ | hρ
  · calc _ ≤ ∫⁻ z : ℂ, 2 * ENNReal.ofReal (Real.exp (-(‖z‖ ^ 2 / 2))) := by
          refine lintegral_mono fun z => ?_
          calc _ ≤ ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) * ENNReal.ofReal ((‖z‖ ^ 2) ^ p) * 1 := by
                gcongr; exact ballInd_le_one ρ z
            _ = ENNReal.ofReal (Real.exp (-‖z‖ ^ 2) * (‖z‖ ^ 2) ^ p) := by
                rw [mul_one, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
            _ ≤ ENNReal.ofReal (2 * Real.exp (-(‖z‖ ^ 2 / 2))) :=
                ENNReal.ofReal_le_ofReal (exp_mul_pow_le (by positivity) hp)
            _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; simp
      _ = 2 * halfGauss := lintegral_const_mul' _ _ (by simp)
      _ = ENNReal.ofReal (2 * halfGauss.toReal) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hG.ne]; simp
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [le_div_iff₀ hq]
          have h4 : (1 + ρ ^ 2) ^ (p + 1) ≤ 4 :=
            (pow_le_pow_left₀ (by positivity) (by linarith) (p + 1)).trans h24
          unfold entryConst
          nlinarith
  · have hρ0 : 0 < |ρ| := abs_pos.2 (by rintro rfl; norm_num at hρ)
    have hset : {z : ℂ | |ρ| * ‖z‖ < 1} = Metric.ball (0 : ℂ) |ρ|⁻¹ := by
      ext z
      simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
      rw [← one_div, lt_div_iff₀ hρ0, mul_comm]
    have hu : (|ρ|⁻¹) ^ 2 = (ρ ^ 2)⁻¹ := by rw [inv_pow, sq_abs]
    calc _ ≤ ∫⁻ z : ℂ, ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p) *
          (Metric.ball (0 : ℂ) |ρ|⁻¹).indicator 1 z := by
          refine lintegral_mono fun z => ?_
          unfold ballInd
          rw [hset]
          by_cases hz : z ∈ Metric.ball (0 : ℂ) |ρ|⁻¹
          · rw [Set.indicator_of_mem hz]
            have hz' : ‖z‖ ^ 2 ≤ (ρ ^ 2)⁻¹ := by
              rw [Metric.mem_ball, dist_zero_right] at hz
              rw [← hu]; exact pow_le_pow_left₀ (norm_nonneg _) hz.le 2
            have he : ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) ≤ 1 :=
              ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg z]))
            calc _ ≤ 1 * ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p) * 1 := by
                  gcongr
                  simp
              _ = _ := by simp
          · rw [Set.indicator_of_notMem hz]; simp
      _ = ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p) * volume (Metric.ball (0 : ℂ) |ρ|⁻¹) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_one measurableSet_ball]
      _ = ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p * ((ρ ^ 2)⁻¹ * Real.pi)) := by
          rw [Complex.volume_ball, ← ENNReal.ofReal_pow (inv_nonneg.2 hρ0.le), hu,
            ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [le_div_iff₀ hq]
          have hρ2 : 0 < ρ ^ 2 := by linarith
          have hu1 : (ρ ^ 2)⁻¹ * ρ ^ 2 = 1 := inv_mul_cancel₀ hρ2.ne'
          have hu0 : 0 < (ρ ^ 2)⁻¹ := inv_pos.2 hρ2
          have hule : (ρ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ.le
          have key : (ρ ^ 2)⁻¹ * (1 + ρ ^ 2) = (ρ ^ 2)⁻¹ + 1 := by rw [mul_add, hu1, mul_one]
          have h2 : ((ρ ^ 2)⁻¹) ^ p * ((ρ ^ 2)⁻¹ * Real.pi) * (1 + ρ ^ 2) ^ (p + 1) =
              Real.pi * ((ρ ^ 2)⁻¹ + 1) ^ (p + 1) := by
            rw [← key, mul_pow]; ring
          have h3 : ((ρ ^ 2)⁻¹ + 1) ^ (p + 1) ≤ 4 :=
            (pow_le_pow_left₀ (by positivity) (by linarith) (p + 1)).trans h24
          rw [h2]
          unfold entryConst
          nlinarith
end GroundTheory.Heights₂.Heights.LeadBlockGaussTail
