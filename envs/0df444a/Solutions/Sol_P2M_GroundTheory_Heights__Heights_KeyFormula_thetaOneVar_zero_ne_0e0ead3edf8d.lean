-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_thetaOneVar_zero_ne_0e0ead3edf8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:39.366625+00:00
-- url     : https://prove2.me/submissions/f1261293-490e-4992-b4a0-b0d9074cbbb5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution : thetaOneVar 0 ≠ 0 := by
  intro h
  have hb := norm_jacobiTheta_sub_one_le (τ := I) (by simp)
  rw [jacobiTheta_eq_jacobiTheta₂] at hb
  simp only [thetaOneVar, Pi.zero_apply] at h
  rw [h] at hb
  simp only [zero_sub, norm_neg, norm_one, Complex.I_im, mul_one] at hb
  have hπ : 3 < Real.exp Real.pi := by
    have := Real.add_one_le_exp Real.pi
    linarith [Real.pi_gt_three]
  have ht : Real.exp (-Real.pi) < 1 / 3 := by
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    simpa using hπ
  have htpos := Real.exp_pos (-Real.pi)
  have h1 : 0 < 1 - Real.exp (-Real.pi) := by linarith
  have : 2 / (1 - Real.exp (-Real.pi)) * Real.exp (-Real.pi) < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one h1]; linarith
  linarith
end GroundTheory.Heights₂.Heights.KeyFormula
