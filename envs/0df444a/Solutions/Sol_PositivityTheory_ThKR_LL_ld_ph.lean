-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.ld_ph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:35.143043+00:00
-- url     : https://prove2.me/submissions/f0707b1f-a777-4727-b290-00322f23b977

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Theorems.Thm_PositivityTheory_ThKR_LL_mq_apply
import Theorems.Thm_PositivityTheory_ThKR_LL_norm_exp_sub_le
import Theorems.Thm_PositivityTheory_ThKR_LL_exists_lip
import Theorems.Thm_PositivityTheory_ThKR_LL_exists_decay
import Theorems.Thm_PositivityTheory_ThKR_LL_hasDerivAt_schwartz_to_L2
import Theorems.Thm_PositivityTheory_ThKR_LL_ph_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution {S : ℝ → Eu l →L[ℝ] Eu l} {S' : Eu l →L[ℝ] Eu l} {t₀ : ℝ} (h : HasDerivAt S S' t₀) :
    LD (fun t => ph (S t)) (fun f => mq S' (ph (S t₀) f)) t₀ := fun f => by
  obtain ⟨K, hK, hb⟩ := exists_lip h
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  obtain ⟨C, hC, hf⟩ := exists_decay f (N + 2)
  refine hasDerivAt_schwartz_to_L2 (C := π * K * C) (fun x => ?_) ?_
  · simp only [ph_apply, mq_apply]
    have h1 : HasDerivAt (fun t => S t x) (S' x) t₀ := by simpa using h.clm_apply (hasDerivAt_const t₀ x)
    have h2 : HasDerivAt (fun t => ⟪x, S t x⟫) ⟪x, S' x⟫ t₀ := (innerSL ℝ x).hasFDerivAt.comp_hasDerivAt t₀ h1
    exact (((h2.const_mul (-π)).ofReal_comp.mul_const I).cexp.mul_const (f x)).congr_deriv (by ring)
  · filter_upwards [hb] with t ht x
    rw [← hN]
    simp only [ph_apply]
    rw [← sub_mul, norm_mul]
    have h1 : |-π * ⟪x, S t x⟫ - -π * ⟪x, S t₀ x⟫| ≤ π * ((1 + ‖x‖) ^ 2 * (K * |t - t₀|)) := by
      rw [← mul_sub, ← inner_sub_right, abs_mul, abs_neg, abs_of_pos Real.pi_pos, ← ContinuousLinearMap.sub_apply]
      refine mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans ?_) Real.pi_pos.le
      have h2 := (S t - S t₀).le_opNorm x
      calc ‖x‖ * ‖(S t - S t₀) x‖ ≤ ‖x‖ * ((K * |t - t₀|) * ‖x‖) := by
            refine mul_le_mul_of_nonneg_left (h2.trans ?_) (norm_nonneg _)
            gcongr
        _ = ‖x‖ ^ 2 * (K * |t - t₀|) := by ring
        _ ≤ _ := by gcongr; simp
    calc _ ≤ (1 + ‖x‖) ^ N * (π * ((1 + ‖x‖) ^ 2 * (K * |t - t₀|)) * ‖f x‖) := by
          gcongr
          exact (norm_exp_sub_le _ _).trans h1
      _ = π * K * ((1 + ‖x‖) ^ (N + 2) * ‖f x‖) * |t - t₀| := by ring
      _ ≤ _ := by gcongr; exact hf x
end PositivityTheory.ThKR.LL
