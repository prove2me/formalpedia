-- Prove2me | solution 1 for PI.lp_shift_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:21:30.126047+00:00
-- url     : https://prove2.me/submissions/0838dbbe-0271-4313-8a6c-f016765834c1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LpLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LinearProgramLowerBound_LpFeasibleLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI
open Finset
namespace PI
theorem _root_.solution (d : ℕ) [NeZero d] (xs : ZMod d → ℕ → ℝ) :
    ∑ s, ∑ i ∈ range d, xs (s - (i : ZMod d)) i = ∑ s, ∑ i ∈ range d, xs s i := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun s => rfl)
end PI
