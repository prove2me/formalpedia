-- Prove2me | solution 1 for Parikh.ParseTree.mem_support_plug
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:30.181812+00:00
-- url     : https://prove2.me/submissions/459ceacc-a6ce-49e5-bf48-71bfde1904c9

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
theorem _root_.solution (E t : ParseTree T N) (A : N) :
    A ∈ (E.plug t).support ↔ A ∈ E.support ∨ (E.holes ≠ [] ∧ A ∈ t.support) := by
  classical
  induction E using ParseTree.rec (motive_2 := fun (cs : List (ParseTree T N)) =>
    ∀ c ∈ cs, A ∈ (c.plug t).support ↔
      A ∈ c.support ∨ (c.holes ≠ [] ∧ A ∈ t.support)) with
  | terminal a => simp [plug.eq_1, support, productionLabels.eq_1, holes.eq_1]
  | hole B => simp [plug.eq_2, support, productionLabels.eq_2, holes.eq_2]
  | node r cs ih =>
    have hholes : (node r cs).holes ≠ [] ↔ ∃ c ∈ cs, c.holes ≠ [] := by
      simp only [holes.eq_3, ne_eq, List.flatten_eq_nil_iff, List.forall_mem_map]
      push Not
      rfl
    have hlabels : ∀ c ∈ cs,
        A ∈ (c.plug t).productionLabels ↔
          A ∈ c.productionLabels ∨ (c.holes ≠ [] ∧ A ∈ t.productionLabels) := ih
    simp only [plug.eq_3, support, productionLabels.eq_3, List.map_map, Set.mem_ofPred_eq,
      List.mem_cons, ← List.flatMap_def, List.mem_flatMap, hholes]
    aesop
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs d hd
end Parikh.ParseTree
