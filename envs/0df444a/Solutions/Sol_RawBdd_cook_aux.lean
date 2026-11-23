-- Prove2me | solution 1 for RawBdd.cook_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:00:46.098229+00:00
-- url     : https://prove2.me/submissions/f6b7c579-51f5-4e66-9ab7-402fba513a50

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
open RawBdd
namespace RawBdd
theorem _root_.solution {n : Nat} {j : Fin n} {a : Nat} {hj : (j : Nat) < a} {p : RawPointer} {h1 : p.Bounded n} {h2 : p.Bounded a} : p.cook h1 = .node j → p.cook h2 = .node ⟨j, hj⟩ := by
  intro h
  cases p with
  | inl val => simp_all [RawPointer.cook]
  | inr val =>
    simp_all [RawPointer.cook]
    rw [Fin.eq_mk_iff_val_eq] at h
    exact h
end RawBdd
