-- Prove2me | solution 1 for Parikh.mem_treeFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:59.169105+00:00
-- url     : https://prove2.me/submissions/d41d963c-c5f2-4b0e-8d26-16408816efe3

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Theorems.Thm_Parikh_ParseTree_height_child_lt
public import Theorems.Thm_Parikh_ParseTree_mem_nodeFamily

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} [Fintype T]
namespace Parikh
theorem _root_.solution (g : ContextFreeGrammar T) (H : ℕ) (t : ParseTree T g.NT)
    (ht : ActiveOpen g t) (hh : t.height ≤ H) : t ∈ treeFamily g H := by
  classical
  induction H generalizing t with
  | zero =>
    cases ht.1 with
    | terminal a => simp [treeFamily, treeLeaves]
    | hole A =>
      have hA := ht.2 A (by simp only [ParseTree.holes.eq_2, List.mem_singleton])
      simp [treeFamily, treeLeaves, hA]
    | node r cs hr hv roots => rw [ParseTree.height.eq_3] at hh; omega
  | succ H ih =>
    cases ht.1 with
    | terminal a => simp [treeFamily, treeLeaves]
    | hole A =>
      have hA := ht.2 A (by simp only [ParseTree.holes.eq_2, List.mem_singleton])
      simp [treeFamily, treeLeaves, hA]
    | node r cs hr hv roots =>
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨r, hr, ParseTree.mem_nodeFamily r _ cs ?_ ?_⟩
      · simpa using congrArg List.length roots
      · intro c hc
        have hchild := ParseTree.height_child_lt r cs c hc
        apply ih c ⟨hv c hc, ?_⟩ (by omega)
        intro A hA
        apply ht.2 A
        simp only [ParseTree.holes.eq_3, ← List.flatMap_def, List.mem_flatMap]
        exact ⟨c, hc, hA⟩
end Parikh
