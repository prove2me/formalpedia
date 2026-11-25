-- Prove2me | solution 1 for PI.TailWork.log_four_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:44.293714+00:00
-- url     : https://prove2.me/submissions/691948a6-8883-4d01-b578-4af8e30fbdbc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.TailWork
open Finset
namespace PI.TailWork
theorem _root_.solution : Real.log 4 < 1.3863 := by
  have h2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  norm_num at h2 ⊢
  linarith
end PI.TailWork
