-- Prove2me | solution 1 for SinkReset.exists_isAk_reset_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:48.620692+00:00
-- url     : https://prove2.me/submissions/8f8bc9ef-9da5-4aaf-bc03-32d32b3d8ac7

module
public import Mathlib
public import Definitions.Def_SinkReset
public import Definitions.Def_SinkResetThresholds_Solution
public import Theorems.Thm_SinkReset_exists_isAk_reset_ge_dev


set_option autoImplicit false
@[expose] public section
public section
open SinkReset
namespace SinkReset
theorem _root_.solution (n k : ℕ) [NeZero n] (hn : 2 ≤ n) (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) : ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length :=
  exists_isAk_reset_ge_dev n k hn hk hnk
end SinkReset
