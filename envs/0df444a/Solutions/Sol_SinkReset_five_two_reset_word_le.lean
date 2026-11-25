-- Prove2me | solution 1 for SinkReset.five_two_reset_word_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:50.797799+00:00
-- url     : https://prove2.me/submissions/2c388228-1cee-4135-8aca-aa990e6086be

module
public import Mathlib
public import Definitions.Def_SinkReset
public import Definitions.Def_SinkResetThresholds_Solution
public import Theorems.Thm_SinkReset_five_two_reset_word_le_dev


set_option autoImplicit false
@[expose] public section
public section
open SinkReset
namespace SinkReset
theorem _root_.solution (A : Automaton 5) (hA : A.IsAk 2) : ∃ w, A.IsReset w ∧ w.length ≤ 6 :=
  five_two_reset_word_le_dev A hA
end SinkReset
