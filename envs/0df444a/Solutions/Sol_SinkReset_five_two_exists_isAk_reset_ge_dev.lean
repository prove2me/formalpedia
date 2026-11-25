-- Prove2me | solution 1 for SinkReset.five_two_exists_isAk_reset_ge_dev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:51:39.350669+00:00
-- url     : https://prove2.me/submissions/dd38e7e7-cf02-4c90-aaae-5570a04ecbaf

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_exists_isAk_reset_ge_dev

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
namespace SinkReset
theorem _root_.solution : ∃ A : Automaton 5, A.IsAk 2 ∧ ∀ w, A.IsReset w → 6 ≤ w.length := by
  have h : f 2 5 = 6 := by simp [f, Finset.sum_range_succ]
  rw [← h]
  exact exists_isAk_reset_ge_dev 5 2 (by norm_num) (by norm_num) (by norm_num)
end SinkReset
