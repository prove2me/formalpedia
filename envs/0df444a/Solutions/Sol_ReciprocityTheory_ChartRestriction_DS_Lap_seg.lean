-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.seg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:25:18.292328+00:00
-- url     : https://prove2.me/submissions/4380f66f-4d15-414b-9a09-1574d2e41aaf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution : SegStatement := by
  intro n Q x s d N hx hstep
  have key : ∀ m : ℕ, m ≤ N → Q (x + ((m : ℝ) * d) • Pi.single s 1) := by
    intro m
    induction m with
    | zero => intro _; simpa using hx
    | succ m ih =>
      intro hm
      have h := hstep m (by omega) (ih (by omega))
      rw [Nat.cast_succ]
      exact h
  exact key N le_rfl
end ReciprocityTheory.ChartRestriction.DS.Lap
