-- Prove2me | solution 1 for OBdd.Canonicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:07:03.584087+00:00
-- url     : https://prove2.me/submissions/9552418f-57ea-4169-9123-48231bb60dbb

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_P2M_OBdd_evaluate_terminal__321343d95937
import Theorems.Thm_OBdd_independentOf_lt_root
import Theorems.Thm_OBdd_high_reduced
import Theorems.Thm_OBdd_low_reduced
import Theorems.Thm_OBdd_evaluate_high_eq_evaluate_low_of_independentOf_root
import Theorems.Thm_OBdd_evaluate_high_eq_evaluate_set_true
import Theorems.Thm_OBdd_evaluate_low_eq_evaluate_set_false
import Theorems.Thm_P2M_OBdd_evaluate_high_eq_of_evaluate_eq_and_var_eq__03e8ec3bc298
import Theorems.Thm_P2M_OBdd_evaluate_low_eq_of_evaluate_eq_and_var_eq__6f138cebfdfe
import Theorems.Thm_OBdd_not_reduced_of_sim_high_low
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} {U : OBdd n m'} (ho : O.Reduced) (hu : U.Reduced) :
    O.evaluate = U.evaluate → O.HSimilar U := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b =>
    cases U_root_def : U.1.root with
    | terminal c =>
      simp only [HSimilar]
      rcases O with ⟨⟨heap, root⟩, o⟩
      rcases U with ⟨⟨ueap, uoot⟩, u⟩
      simp_all
    | node i =>
      rw [evaluate_terminal' O_root_def] at h
      have : (U.high U_root_def).evaluate = (U.low U_root_def).evaluate := by
        ext I
        trans b
        · rw [evaluate_high_eq_evaluate_set_true]
          rw [← h]
          simp
        · rw [evaluate_low_eq_evaluate_set_false]
          rw [← h]
          simp
      absurd hu
      apply not_reduced_of_sim_high_low U_root_def
      apply solution (high_reduced hu) (low_reduced hu) this
  | node j =>
    cases U_root_def : U.1.root with
    | terminal c =>
      rw [evaluate_terminal' U_root_def] at h
      have : (O.high O_root_def).evaluate = (O.low O_root_def).evaluate := by
        ext I
        trans c
        · rw [evaluate_high_eq_evaluate_set_true]
          rw [h]
          simp
        · rw [evaluate_low_eq_evaluate_set_false]
          rw [h]
          simp
      absurd ho
      apply not_reduced_of_sim_high_low O_root_def
      apply solution (high_reduced ho) (low_reduced ho) this
    | node i =>
      simp only [HSimilar]
      rw [toTree_node O_root_def, toTree_node U_root_def]
      simp only [Ordered, DecisionTree.branch.injEq]
      have same_var : O.1.heap[j].var = U.1.heap[i].var := by
        apply eq_iff_le_not_lt.mpr
        constructor
        · apply le_of_not_gt
          intro contra
          have := independentOf_lt_root O ⟨U.1.heap[i].var.1, by simp only [Fin.getElem_fin, var, Nat.succ_eq_add_one, Bdd.var]; rw [O_root_def]; simpa⟩
          rw [h] at this
          simp only [Fin.eta] at this
          simp only [Nary.IndependentOf] at this
          have that : OBdd.Similar (U.high U_root_def) (U.low U_root_def) :=
            solution (high_reduced hu) (low_reduced hu) (evaluate_high_eq_evaluate_low_of_independentOf_root this)
          apply hu.1 U.1.toRelevantPointer
          simp [toRelevantPointer]
          rw [U_root_def]
          constructor
          have iso : SimilarRP U ⟨(U.high U_root_def).1.root, reachable_of_edge (edge_of_high (h := U_root_def) U.1)⟩
                                  ⟨(U.low  U_root_def).1.root, reachable_of_edge (edge_of_low  (h := U_root_def) U.1)⟩ := that
          exact (symm (hu.2 iso))
        · intro contra
          have := independentOf_lt_root U ⟨O.1.heap[j].var.1, by simp only [Fin.getElem_fin, var, Nat.succ_eq_add_one, Bdd.var]; rw [U_root_def]; simpa⟩
          rw [← h] at this
          simp only [Ordered, Fin.eta] at this
          simp only [Nary.IndependentOf] at this
          have that : OBdd.Similar (O.high O_root_def) (O.low O_root_def) :=
            solution (high_reduced ho) (low_reduced ho) (evaluate_high_eq_evaluate_low_of_independentOf_root this)
          apply ho.1 O.1.toRelevantPointer
          simp [toRelevantPointer]
          rw [O_root_def]
          constructor
          have iso : SimilarRP O ⟨(O.high O_root_def).1.root, reachable_of_edge (edge_of_high (h := O_root_def) O.1)⟩
                                  ⟨(O.low  O_root_def).1.root, reachable_of_edge (edge_of_low  (h := O_root_def) O.1)⟩ := that
          exact (symm (ho.2 iso))
      constructor
      · exact same_var
      · constructor
        · apply solution (low_reduced  ho) (low_reduced  hu) (evaluate_low_eq_of_evaluate_eq_and_var_eq'  h same_var)
        · apply solution (high_reduced ho) (high_reduced hu) (evaluate_high_eq_of_evaluate_eq_and_var_eq' h same_var)
termination_by O.size' + U.size'
decreasing_by
  simp [size_node U_root_def]; omega
  simp [size_node O_root_def]; omega
  all_goals
    simp [size_node O_root_def, size_node U_root_def]; omega
end OBdd
