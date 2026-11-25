-- Prove2me | solution 1 for PI.TailWork.w_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:38.638815+00:00
-- url     : https://prove2.me/submissions/791cb834-0b04-4753-a1aa-8f61e505ee6e

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
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) : 0 ≤ g n - g (n + 1) := by
  unfold g
  have h1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  rw [sub_nonneg]
  apply one_div_le_one_div_of_le
  · nlinarith
  · nlinarith
end PI.TailWork
