-- Prove2me | solution 1 for Parikh.ParseTree.height_le_height_plug
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:20.242493+00:00
-- url     : https://prove2.me/submissions/c42a150d-f082-4980-95e3-537585f340bf

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
open Parikh.ParseTree
namespace Parikh.ParseTree
theorem _root_.solution (E t : ParseTree T N) : E.height ≤ (E.plug t).height := by
  induction E using ParseTree.rec (motive_2 := fun cs =>
    ∀ c ∈ cs, c.height ≤ (c.plug t).height) with
  | terminal a => simp [height, plug]
  | hole A => simp [height, plug]
  | node r cs ih =>
    simp only [plug, height, List.map_map, List.foldl_map]
    apply Nat.add_le_add_left
    exact List.foldl_rel (r := (· ≤ ·)) (Nat.le_refl 0)
      (fun c hc a b hab => max_le_max hab (ih c hc))
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs d hd
end Parikh.ParseTree
