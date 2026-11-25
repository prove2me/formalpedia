-- Prove2me | solution 1 for SinkReset.reset_word_le_of_isAk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:25.8979+00:00
-- url     : https://prove2.me/submissions/4dbace75-aad3-4c5b-860b-bb7abb2a309b

module
public import Mathlib
public import Definitions.Def_SinkReset
public import Definitions.Def_SinkResetThresholds_Solution
public import Theorems.Thm_SinkReset_reset_word_le_of_isAk_dev


set_option autoImplicit false
@[expose] public section
public section
open SinkReset
namespace SinkReset
theorem _root_.solution (n k : ℕ) [NeZero n] (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) (A : Automaton n) (hA : A.IsAk k) : ∃ w, A.IsReset w ∧ w.length ≤ f k n :=
  reset_word_le_of_isAk_dev n k hk hnk A hA
end SinkReset
