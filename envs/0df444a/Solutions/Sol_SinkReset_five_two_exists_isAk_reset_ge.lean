-- Prove2me | solution 1 for SinkReset.five_two_exists_isAk_reset_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:08.923406+00:00
-- url     : https://prove2.me/submissions/0e66903d-0f3a-4544-98ff-3e3c47e21864

module
public import Mathlib
public import Definitions.Def_SinkReset
public import Definitions.Def_SinkResetThresholds_Solution
public import Theorems.Thm_SinkReset_five_two_exists_isAk_reset_ge_dev


set_option autoImplicit false
@[expose] public section
public section
open SinkReset
namespace SinkReset
theorem _root_.solution : ∃ A : Automaton 5, A.IsAk 2 ∧ ∀ w, A.IsReset w → 6 ≤ w.length :=
  five_two_exists_isAk_reset_ge_dev
end SinkReset
