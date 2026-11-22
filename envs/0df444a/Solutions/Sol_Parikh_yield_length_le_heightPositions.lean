-- Prove2me | solution 1 for Parikh.yield_length_le_heightPositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:09.129472+00:00
-- url     : https://prove2.me/submissions/ec34c8eb-654e-45fa-97cd-8514f4dca0eb

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Theorems.Thm_Parikh_heightPositions_zero
public import Theorems.Thm_Parikh_heightPositions_succ
public import Theorems.Thm_Parikh_heightPositions_pos
public import Theorems.Thm_Parikh_ParseTree_height_child_lt

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} [Fintype T]
omit [Fintype T]
namespace Parikh
theorem _root_.solution (g : ContextFreeGrammar T) (b : ℕ)
    (hb : ∀ r ∈ g.rules, r.output.length ≤ b) (H : ℕ) (t : ParseTree T g.NT)
    (hv : Valid g t) (hh : t.height ≤ H) : t.yield.length ≤ heightPositions b H := by
  induction H generalizing t with
  | zero =>
    cases hv with
    | terminal a => simp [ParseTree.yield.eq_1, heightPositions_zero]
    | hole A => simp only [ParseTree.yield.eq_2, List.length_nil, Nat.zero_le]
    | node r cs hr hc roots => rw [ParseTree.height.eq_3] at hh; omega
  | succ H ih =>
    cases hv with
    | terminal a => simpa only [ParseTree.yield.eq_1, List.length_singleton] using
      heightPositions_pos b (H + 1)
    | hole A => simp only [ParseTree.yield.eq_2, List.length_nil, Nat.zero_le]
    | node r cs hr hc roots =>
      have hlen : cs.length ≤ b := by
        have := congrArg List.length roots
        simpa using this.le.trans (hb r hr)
      have hchildren : ∀ n ∈ cs.map (fun c => c.yield.length), n ≤ heightPositions b H := by
        intro n hn
        obtain ⟨c, hmem, rfl⟩ := List.mem_map.mp hn
        have hchild := ParseTree.height_child_lt r cs c hmem
        exact ih c (hc c hmem) (by omega)
      calc
        (ParseTree.node r cs).yield.length = (cs.map (fun c => c.yield.length)).sum := by
          simp only [ParseTree.yield.eq_3, List.length_flatten, List.map_map, Function.comp_def]
        _ ≤ cs.length * heightPositions b H := by
          have bound : ∀ l : List ℕ, (∀ n ∈ l, n ≤ heightPositions b H) →
              l.sum ≤ l.length * heightPositions b H := by
            intro l
            induction l with
            | nil => simp
            | cons a l ih =>
              intro hl
              have ha := hl a (by simp)
              have ht := ih (fun n hn => hl n (by simp [hn]))
              simp only [List.sum_cons, List.length_cons]
              rw [Nat.add_mul, one_mul]
              omega
          simpa only [List.length_map] using bound _ hchildren
        _ ≤ b * heightPositions b H := Nat.mul_le_mul_right _ hlen
        _ ≤ heightPositions b (H + 1) := by rw [heightPositions_succ]; omega
end Parikh
