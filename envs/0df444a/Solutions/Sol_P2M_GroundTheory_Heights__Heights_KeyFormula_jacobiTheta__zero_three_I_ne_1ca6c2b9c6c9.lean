-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_jacobiTheta__zero_three_I_ne_1ca6c2b9c6c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:32.98485+00:00
-- url     : https://prove2.me/submissions/54fb9905-9679-4e3b-8f71-f42080351273

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_im_three_I_pos_32484545ae83

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
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution : jacobiTheta₂ 0 (3 * I) ≠ 0 := by
  intro h
  have hb := norm_jacobiTheta_sub_one_le (τ := 3 * I) im_three_I_pos
  rw [jacobiTheta_eq_jacobiTheta₂, h] at hb
  simp only [zero_sub, norm_neg, norm_one] at hb
  have him : (3 * I).im = 3 := by simp
  rw [him] at hb
  have hπ : 3 < Real.exp (Real.pi * 3) := by
    have := Real.add_one_le_exp (Real.pi * 3)
    nlinarith [Real.pi_gt_three]
  have ht : Real.exp (-Real.pi * 3) < 1 / 3 := by
    rw [show -Real.pi * 3 = -(Real.pi * 3) by ring, Real.exp_neg,
      inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    simpa using hπ
  have htpos := Real.exp_pos (-Real.pi * 3)
  have h1 : 0 < 1 - Real.exp (-Real.pi * 3) := by linarith
  have : 2 / (1 - Real.exp (-Real.pi * 3)) * Real.exp (-Real.pi * 3) < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one h1]; linarith
  linarith
end GroundTheory.Heights₂.Heights.KeyFormula
