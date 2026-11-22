-- Prove2me | solution 1 for Parikh.card_treeFamily_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:49.279941+00:00
-- url     : https://prove2.me/submissions/7c56f66e-f19f-48c5-b478-0ecccff0eb91

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Theorems.Thm_Parikh_heightPositions_zero
public import Theorems.Thm_Parikh_heightPositions_succ
public import Theorems.Thm_Parikh_ParseTree_card_nodeFamily_le
public import Theorems.Thm_Parikh_card_treeLeaves_le

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} [Fintype T]
namespace Parikh
theorem _root_.solution (g : ContextFreeGrammar T) (b q : ℕ)
    (hq : 1 + Fintype.card T + (activeNonterminals g).card + g.rules.card ≤ q)
    (hb : ∀ r ∈ g.rules, r.output.length ≤ b) (H : ℕ) :
    (treeFamily g H).card ≤ q ^ heightPositions b H := by
  classical
  have hq1 : 1 ≤ q := by omega
  induction H with
  | zero => simpa [treeFamily, heightPositions_zero] using (card_treeLeaves_le g).trans (by omega)
  | succ H ih =>
    let A := q ^ heightPositions b H
    have hA : 1 ≤ A ^ b := one_le_pow₀ (one_le_pow₀ hq1)
    have hnodes : ∀ r ∈ g.rules,
        (ParseTree.nodeFamily r (treeFamily g H)).card ≤ A ^ b := by
      intro r hr
      exact (ParseTree.card_nodeFamily_le r _).trans
        ((Nat.pow_le_pow_left ih _).trans (pow_le_pow_right₀ (one_le_pow₀ hq1) (hb r hr)))
    calc
      (treeFamily g (H + 1)).card
          ≤ (treeLeaves g).card + ∑ r ∈ g.rules,
              (ParseTree.nodeFamily r (treeFamily g H)).card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
      _ ≤ (Fintype.card T + (activeNonterminals g).card) + g.rules.card * A ^ b := by
        exact Nat.add_le_add (card_treeLeaves_le g) (by
          simpa using Finset.sum_le_sum hnodes)
      _ ≤ q * A ^ b := by
        have hl := Nat.mul_le_mul_left (Fintype.card T + (activeNonterminals g).card) hA
        have hq' : Fintype.card T + (activeNonterminals g).card + g.rules.card ≤ q := by omega
        calc
          _ ≤ (Fintype.card T + (activeNonterminals g).card) * A ^ b +
              g.rules.card * A ^ b := Nat.add_le_add_right (by simpa using hl) _
          _ = (Fintype.card T + (activeNonterminals g).card + g.rules.card) * A ^ b :=
            (Nat.add_mul _ _ _).symm
          _ ≤ q * A ^ b := Nat.mul_le_mul_right _ hq'
      _ = q ^ heightPositions b (H + 1) := by
        dsimp [A]
        rw [heightPositions_succ, pow_add, pow_one, Nat.mul_comm b, ← pow_mul]
end Parikh
