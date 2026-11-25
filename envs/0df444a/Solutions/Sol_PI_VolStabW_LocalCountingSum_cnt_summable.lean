-- Prove2me | solution 1 for PI.VolStabW.LocalCountingSum.cnt_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:01.712436+00:00
-- url     : https://prove2.me/submissions/13cfebcb-7735-4187-9fc7-c69cd47e27db

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensQ
import Theorems.Thm_PI_VolStabW_LocalCountingSum_sum_cnt_bigO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors
open PI.VolStabW.LocalCountingSum
variable (K : Type) [Field K] [NumberField K]
namespace PI.VolStabW.LocalCountingSum
theorem _root_.solution : Summable fun n : ℕ ↦ cnt K n / (n : ℝ) ^ 2 := by
  have hL := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := 2) (sum_cnt_bigO K)
    (fun n ↦ by unfold cnt; positivity) zero_le_one (by norm_num)
  refine hL.norm.congr fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold cnt; positivity)]
    norm_num
end PI.VolStabW.LocalCountingSum
