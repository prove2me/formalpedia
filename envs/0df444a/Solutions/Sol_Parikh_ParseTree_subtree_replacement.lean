-- Prove2me | solution 1 for Parikh.ParseTree.subtree_replacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:21.929694+00:00
-- url     : https://prove2.me/submissions/e3bba21f-ac29-4bf1-9047-5971ab518f53

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
theorem _root_.solution (t : ParseTree T N) (q : List ℕ) (u v : ParseTree T N)
    (hpos : t.subtree q = some u) :
    ∃ t', t.replaceAt q v = some t' ∧ t'.subtree q = some v ∧
      t'.replaceAt q u = some t := by
  induction q generalizing t with
  | nil =>
    simp only [subtree, Option.some.injEq] at hpos
    subst u
    exact ⟨v, rfl, rfl, rfl⟩
  | cons i q ih =>
    cases t with
    | terminal a => simp [subtree] at hpos
    | hole A => simp [subtree] at hpos
    | node r cs =>
      obtain ⟨c, hi, hpos⟩ := Option.bind_eq_some_iff.mp hpos
      obtain ⟨c', hreplace, hsub, hundo⟩ := ih c hpos
      obtain ⟨hlt, helem⟩ := List.getElem?_eq_some_iff.mp hi
      have hset : cs.set i c = cs := by
        rw [← helem]
        exact List.set_getElem_self hlt
      refine ⟨.node r (cs.set i c'), ?_, ?_, ?_⟩
      · simp [replaceAt, hi, hreplace]
      · simp [subtree, List.getElem?_set_self hlt, hsub]
      · simp [replaceAt, List.getElem?_set_self hlt, hundo, List.set_set, hset]
end Parikh.ParseTree
