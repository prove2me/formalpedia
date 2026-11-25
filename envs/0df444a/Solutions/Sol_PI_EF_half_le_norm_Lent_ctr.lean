-- Prove2me | solution 1 for PI.EF.half_le_norm_Lent_ctr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:45.978146+00:00
-- url     : https://prove2.me/submissions/28228cbf-de2b-4661-8e6d-98bdc4447377

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Theorems.Thm_PI_EF_Lent_eq
import Theorems.Thm_PI_EF_ctr_re
import Theorems.Thm_PI_EF_ctr_ne_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.EF.ctr_re

set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution (hI : PI.LInvRight) (χ : DirichletCharacter ℂ N) (t : ℝ) :
    1 / 2 ≤ ‖Lent χ (ctr t)‖ := by
  have hL := hI N χ (ctr t) (by rw [ctr_re]; norm_num)
  have h21 : (2 : ℝ) / (2 - 1) = 2 := by norm_num
  rw [ctr_re, h21] at hL
  have hne := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (s := ctr t)
    (Or.inr (ctr_ne_one t)) (by rw [ctr_re]; norm_num)
  have hpos : 0 < ‖LFunction χ (ctr t)‖ := norm_pos_iff.mpr hne
  have hL2 : 1 / 2 ≤ ‖LFunction χ (ctr t)‖ := by
    have h1 := mul_le_mul_of_nonneg_left hL hpos.le
    rw [mul_inv_cancel₀ hpos.ne'] at h1
    linarith
  rw [Lent_eq χ (ctr_ne_one t), norm_mul]
  have hf : 1 ≤ ‖1 + del1 χ * (ctr t - 2)‖ := by
    have hre : (1 + del1 χ * (ctr t - 2)).re = 1 := by
      unfold del1 ctr
      split_ifs <;> norm_num
    have := Complex.abs_re_le_norm (1 + del1 χ * (ctr t - 2))
    rw [hre, abs_one] at this
    exact this
  have := mul_le_mul hf hL2 (by norm_num) (by positivity)
  linarith
end PI.EF
