-- Prove2me | solution 1 for SinkReset.Plan.act_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:42:46.924083+00:00
-- url     : https://prove2.me/submissions/44713f77-041f-47be-aa6f-c365c35d623a

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
theorem _root_.solution (w : List (Letter n)) (hw : A.IsWord w) :
    act w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha : a ∈ A.letters := hw a List.mem_cons_self
    have hw' : A.IsWord w := fun b hb => hw b (List.mem_cons_of_mem a hb)
    change act w (a 0) = 0
    rw [A.sink_fixed a ha]
    exact ih hw'
end SinkReset.Plan
