-- Prove2me | solution 1 for Parikh.ParseTree.count_yield_plug
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:27.337094+00:00
-- url     : https://prove2.me/submissions/06f93c53-2131-459e-9fa5-99a237069645

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_TreePlugging

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
open Parikh.ParseTree
namespace Parikh.ParseTree
theorem _root_.solution [DecidableEq T] (E t : ParseTree T N) (a : T) :
    (E.plug t).yield.count a = E.yield.count a + E.holes.length * t.yield.count a := by
  induction E using ParseTree.rec (motive_2 := fun (cs : List (ParseTree T N)) =>
    ∀ c ∈ cs, (c.plug t).yield.count a =
      c.yield.count a + c.holes.length * t.yield.count a) with
  | terminal b => simp [plug.eq_1, yield.eq_1, holes.eq_1]
  | hole A => simp [plug.eq_2, yield.eq_2, holes.eq_2]
  | node r cs ih =>
    simp only [plug.eq_3, yield.eq_3, holes.eq_3, List.count_flatten, List.length_flatten,
      List.map_map,
      Function.comp_def]
    have hs := List.map_congr_left ih
    rw [hs, List.sum_map_add, List.sum_map_mul_right]
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs d hd
end Parikh.ParseTree
