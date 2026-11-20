-- Prove2me | solution 1 for P010.adjacentCount_append_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:43:09.140583+00:00
-- url     : https://prove2.me/submissions/191595ef-bdcd-4b04-ba80-850cdb779797

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



set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (a b : List ℕ) :
    adjacentCount (a ++ b) ≤
      adjacentCount a + adjacentCount b + 1 := by
  induction a with
  | nil => simp [adjacentCount]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases b with
      | nil => simp [adjacentCount]
      | cons y ys =>
        change adjacentCount (x :: y :: ys) ≤
          adjacentCount [x] + adjacentCount (y :: ys) + 1
        rw [adjacentCount_cons_cons]
        have hsingle : adjacentCount [x] = 0 := by rfl
        rw [hsingle]
        split_ifs <;> omega
    | cons y ys =>
      simp only [List.cons_append, adjacentCount_cons_cons] at ih ⊢
      omega
end P010
