-- Prove2me | solution 1 for Parikh.ParseTree.productionSize_plug
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:48.388924+00:00
-- url     : https://prove2.me/submissions/42a2d1a5-3df4-4e89-96f5-4beb671e072b

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
theorem _root_.solution (E t : ParseTree T N) :
    (E.plug t).productionSize = E.productionSize + E.holes.length * t.productionSize := by
  induction E using ParseTree.rec (motive_2 := fun (cs : List (ParseTree T N)) =>
    ∀ c ∈ cs, (c.plug t).productionSize =
      c.productionSize + c.holes.length * t.productionSize) with
  | terminal a => simp [plug.eq_1, productionSize.eq_1, holes.eq_1]
  | hole A => simp [plug.eq_2, productionSize.eq_2, holes.eq_2]
  | node r cs ih =>
    simp only [plug.eq_3, productionSize.eq_3, holes.eq_3, List.length_flatten, List.map_map,
      Function.comp_def]
    have hs := List.map_congr_left ih
    rw [hs, List.sum_map_add, List.sum_map_mul_right]
    omega
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs d hd
end Parikh.ParseTree
