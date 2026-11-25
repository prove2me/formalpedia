-- Prove2me | solution 1 for PI.ExpIntWProof.stepIII_of_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:43.920433+00:00
-- url     : https://prove2.me/submissions/2f41b9fa-08cf-4c57-a27e-db123a4d3fb2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_StepIII
import Theorems.Thm_PI_ExpIntWProof_div_pow_mem
import Theorems.Thm_PI_ExpIntWProof_norm_p


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof
open PI
namespace PI.ExpIntWProof
theorem _root_.solution (h : KeyW) : StepIII := by
  intro p hp x hx hnorm
  obtain ⟨k, hk⟩ := hx
  have hp0 : (p : ℂ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hn : ‖(p : ℂ_[p]) ^ k * x‖ ≤ ((p : ℝ)⁻¹) ^ k := by
    rw [norm_mul, norm_pow, norm_p]
    exact mul_le_of_le_one_right (by positivity) hnorm
  have h3 := div_pow_mem h p k _ hk hn
  rwa [mul_div_cancel_left₀ _ (pow_ne_zero k hp0)] at h3
end PI.ExpIntWProof
