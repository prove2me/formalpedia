-- Prove2me | solution 1 for SinkReset.Plan.act_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:42:36.172224+00:00
-- url     : https://prove2.me/submissions/85cf9d19-7e07-46c1-97a5-5d9bb9862ca4

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
theorem _root_.solution (u v : List (Letter n)) (q : Fin n) :
    act (u ++ v) q = act v (act u q) := by
  simp [act, List.foldl_append]
end SinkReset.Plan
