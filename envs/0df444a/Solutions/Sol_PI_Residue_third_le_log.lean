-- Prove2me | solution 1 for PI.Residue.third_le_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:41.573496+00:00
-- url     : https://prove2.me/submissions/ae8e3715-4c8d-4519-9249-bf0a3f2abe88

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_ThirdLeLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
namespace PI.Residue
theorem _root_.solution : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h3 : Real.exp (1 / 3) ^ 3 ≤ (3 / 2 : ℝ) ^ 3 := by
    rw [← Real.exp_nat_mul]
    have : ((3 : ℕ) : ℝ) * (1 / 3) = 1 := by norm_num
    rw [this]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h3
end PI.Residue
