-- Prove2me | solution 1 for SimpleGraph.Walk.countP_darts_fst_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:43:13.53535+00:00
-- url     : https://prove2.me/submissions/edace64c-45f0-4dfd-a0cb-b31a47177093

module
public import Definitions.Def_Euler_Trail
public import Definitions.Def_Euler_Orientation

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
omit [Fintype V] [DecidableRel G.Adj]
namespace SimpleGraph
namespace Walk
theorem _root_.solution {u w : V} (p : G.Walk u w) (v : V) :
    p.darts.countP (fun d => d.fst = v) + (if w = v then 1 else 0) =
      p.darts.countP (fun d => d.snd = v) + (if u = v then 1 else 0) := by
  induction p with
  | nil => simp
  | cons h q ih =>
    rename_i a b c
    simp only [darts_cons, List.countP_cons]
    have := ih
    by_cases hav : a = v <;> by_cases hbv : b = v <;> simp_all <;> omega
end Walk
end SimpleGraph
