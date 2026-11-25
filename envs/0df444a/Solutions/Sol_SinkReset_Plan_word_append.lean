-- Prove2me | solution 1 for SinkReset.Plan.word_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:42:48.915648+00:00
-- url     : https://prove2.me/submissions/0d4cbfd3-ccaf-4676-b1b7-4ad9835e3aa0

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)
namespace SinkReset.Plan
theorem _root_.solution (u v : List (Letter n)) :
    A.IsWord (u ++ v) ↔ A.IsWord u ∧ A.IsWord v := by
  simp only [Automaton.IsWord, List.mem_append, or_imp, forall_and]
end SinkReset.Plan
