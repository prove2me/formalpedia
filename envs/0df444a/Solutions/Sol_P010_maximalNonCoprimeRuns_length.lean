-- Prove2me | solution 1 for P010.maximalNonCoprimeRuns_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:43:18.75248+00:00
-- url     : https://prove2.me/submissions/49a694c4-d04a-40bf-8aa8-cbcf26a80d02

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_adjacentCount_cons_cons
public import Theorems.Thm_Nat_Prime_maxPrimeFac_eq_self
public import Theorems.Thm_Nat_maxPrimeFac_eq_self_iff
public import Theorems.Thm_Nat_maxPrimeFac_one
public import Theorems.Thm_Nat_maxPrimeFac_pow
public import Theorems.Thm_Nat_maxPrimeFac_zero
public import Theorems.Thm_Nat_one_le_maxPrimeFac_iff
public import Theorems.Thm_Nat_one_lt_maxPrimeFac_iff
attribute [local simp] Nat.Prime.maxPrimeFac_eq_self
attribute [local simp] Nat.maxPrimeFac_eq_self_iff
attribute [local simp] Nat.maxPrimeFac_one
attribute [local simp] Nat.maxPrimeFac_pow
attribute [local simp] Nat.maxPrimeFac_zero
attribute [local simp] Nat.one_le_maxPrimeFac_iff
attribute [local simp] Nat.one_lt_maxPrimeFac_iff


section
@[expose] public section
namespace P010
private theorem splitBy_loop_run_count
    (xs : List ℕ) (b : ℕ) (rev : List ℕ) (parts : List (List ℕ)) :
    (List.splitBy.loop (fun x y : ℕ => decide (¬Nat.Coprime x y))
      xs b rev parts).length =
        parts.length + 1 + adjacentCount (b :: xs) := by
  induction xs generalizing b rev parts with
  | nil =>
    simp [List.splitBy.loop, adjacentCount]
  | cons x xs ih =>
    by_cases hc : Nat.Coprime b x
    · have hr : decide (¬Nat.Coprime b x) = false := by simp [hc]
      simp only [List.splitBy.loop, hr, adjacentCount_cons_cons]
      rw [if_pos hc]
      have hi := ih x [] ((b :: rev).reverse :: parts)
      simp only [List.length_cons] at hi
      omega
    · have hr : decide (¬Nat.Coprime b x) = true := by simp [hc]
      simp only [List.splitBy.loop, hr, adjacentCount_cons_cons]
      rw [if_neg hc]
      have hi := ih x (b :: rev) parts
      omega
end P010
end
end

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (x : ℕ) (xs : List ℕ) :
    (maximalNonCoprimeRuns (x :: xs)).length =
      adjacentCount (x :: xs) + 1 := by
  simpa [maximalNonCoprimeRuns, List.splitBy, Nat.add_comm, Nat.add_left_comm]
    using splitBy_loop_run_count xs x [] []
end P010
