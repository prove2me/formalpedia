-- Prove2me | solution 1 for SinkReset.exists_isAk_reset_ge_dev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:40.744481+00:00
-- url     : https://prove2.me/submissions/fe8b7af5-d74c-43c8-b187-15de9ea881ce

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_lower

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
namespace SinkReset
theorem _root_.solution (n k : ℕ) [NeZero n] (hn : 2 ≤ n) (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) : ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length := by
  refine Plan.lower hn hk ?_
  omega
end SinkReset
