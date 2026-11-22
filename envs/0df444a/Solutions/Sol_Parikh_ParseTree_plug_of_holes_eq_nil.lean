-- Prove2me | solution 1 for Parikh.ParseTree.plug_of_holes_eq_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:30.53689+00:00
-- url     : https://prove2.me/submissions/605761a5-0118-4349-99d7-477acc5d1aca

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_TreeReplacement

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
open Parikh.ParseTree
namespace Parikh.ParseTree
theorem _root_.solution (E t : ParseTree T N) (hE : E.holes = []) :
    E.plug t = E := by
  induction E using ParseTree.rec (motive_2 := fun (cs : List (ParseTree T N)) =>
    ∀ c ∈ cs, c.holes = [] → c.plug t = c) with
  | terminal a => simp [plug]
  | hole A => simp [holes] at hE
  | node r cs ih =>
    have hc : ∀ c ∈ cs, c.holes = [] := by
      simpa only [holes, List.flatten_eq_nil_iff, List.forall_mem_map] using hE
    simp only [plug]
    congr 1
    simpa using List.map_congr_left (fun c h => ih c h (hc c h))
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd hh =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc hh
    · exact hcs d hd hh
end Parikh.ParseTree
