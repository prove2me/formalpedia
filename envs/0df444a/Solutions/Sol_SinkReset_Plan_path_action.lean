-- Prove2me | solution 1 for SinkReset.Plan.path_action
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:30.619395+00:00
-- url     : https://prove2.me/submissions/b9dda9b3-e43f-42fa-98a5-4ef0e5eb0ffe

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem act_nil (q : Fin n) : act ([] : List (Letter n)) q = q := rfl
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)
end Upper
end Plan
end SinkReset
end
end

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
namespace SinkReset.Plan
theorem _root_.solution {n : ℕ} [NeZero n] (w : List (Letter n))
    (hw : (path n).IsWord w) (q : Fin n) :
    (act w q).val = q.val - w.length := by
  induction w generalizing q with
  | nil => simp [act_nil]
  | cons a w ih =>
    have ha : a = predecessor n := hw a List.mem_cons_self
    have hw' : (path n).IsWord w := fun b hb => hw b (List.mem_cons_of_mem a hb)
    change (act w (a q)).val = _
    rw [ih hw', ha, List.length_cons]
    show q.val - 1 - w.length = q.val - (w.length + 1)
    omega
end SinkReset.Plan
