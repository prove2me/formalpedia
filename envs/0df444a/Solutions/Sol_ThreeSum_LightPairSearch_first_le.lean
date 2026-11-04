-- Prove2me | solution 1 for ThreeSum.LightPairSearch.first_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:29:06.674624+00:00
-- url     : https://prove2.me/submissions/7e3f57e4-dc1c-4360-b3e1-db65b3b53e18

import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.DivMod
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_PairFirst

set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
set_option maxHeartbeats 300000
namespace ThreeSum.LightPairSearch
theorem _root_.solution (good : ℕ → Prop) [DecidablePred good] : ∀ k, first good k≤k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [first]; split <;> omega
end ThreeSum.LightPairSearch
