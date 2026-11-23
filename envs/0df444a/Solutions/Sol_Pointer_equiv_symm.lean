-- Prove2me | solution 1 for Pointer.equiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:58:04.31705+00:00
-- url     : https://prove2.me/submissions/93778dec-987d-4fcd-a0b1-0fe74033738e

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace Pointer
theorem _root_.solution {p : Pointer m} : p.equiv q → q.equiv p := by
  simp only [Pointer.equiv]
  simp_all only [Bool.forall_bool, and_imp]
  intro h1 h2 h3
  constructor
  · constructor
    · intro hq
      cases p with
      | terminal b =>
        cases b with
        | false => rfl
        | true => rw [h2 rfl] at hq; simp_all only [terminal.injEq, Bool.true_eq_false]
      | node _ =>
        rcases (h3 _ rfl) with ⟨_, hc⟩
        rw [hc.1] at hq; contradiction
    · intro hq
      cases p with
      | terminal b =>
        cases b with
        | true => rfl
        | false => rw [h1 rfl] at hq; simp_all only [terminal.injEq]
      | node _ =>
        rcases (h3 _ rfl) with ⟨_, hc⟩
        rw [hc.1] at hq; contradiction
  · intro j hj
    cases p with
    | terminal b =>
      cases b with
      | false => rw [h1 rfl] at hj; contradiction
      | true => rw [h2 rfl] at hj; contradiction
    | node j' =>
      rcases h3 j' rfl with ⟨j'', hj1, hj2⟩
      rw [hj1] at hj
      injection hj with heq
      subst heq
      use j'
      simp [hj2]
end Pointer
