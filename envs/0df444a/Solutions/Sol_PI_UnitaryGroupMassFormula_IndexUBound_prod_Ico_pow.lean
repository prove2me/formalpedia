-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.IndexUBound.prod_Ico_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:45.56702+00:00
-- url     : https://prove2.me/submissions/b756c1b1-d03a-4014-ad19-35ba6c578f8d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexUpperBound_OneSubSumLeProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IndexUBound
open Finset
namespace PI.UnitaryGroupMassFormula.IndexUBound
theorem _root_.solution (g : ℝ) (r : ℕ) :
    ∏ i ∈ Ico 1 r, g ^ i = g ^ (r * (r - 1) / 2) := by
  rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_range_id]
  congr 1
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hr]
    simp
end PI.UnitaryGroupMassFormula.IndexUBound
