-- Prove2me | solution 1 for SinkReset.five_two_reset_word_le_dev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:51:37.234945+00:00
-- url     : https://prove2.me/submissions/6ea35d4e-e7da-4098-9769-76a0d37cbe5d

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_reset_word_le_of_isAk_dev

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
namespace SinkReset
theorem _root_.solution (A : Automaton 5) (hA : A.IsAk 2) : ∃ w, A.IsReset w ∧ w.length ≤ 6 := by
  have h : f 2 5 = 6 := by simp [f, Finset.sum_range_succ]
  rw [← h]
  exact reset_word_le_of_isAk_dev 5 2 (by norm_num) (by norm_num) A hA
end SinkReset
