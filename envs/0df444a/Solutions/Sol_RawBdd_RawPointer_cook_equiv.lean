-- Prove2me | solution 1 for RawBdd.RawPointer.cook_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:56:09.060816+00:00
-- url     : https://prove2.me/submissions/02c21e71-d8ae-4a9a-a887-75bb120258c1

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
namespace RawPointer
theorem _root_.solution {h1 : RawPointer.Bounded m1 p} {h2 : RawPointer.Bounded m2 p} : Pointer.equiv (RawPointer.cook p h1) (RawPointer.cook p h2) := by
  simp only [Pointer.equiv]
  constructor
  · intro b hb
    cases p <;> simp_all [RawPointer.cook]
  · intro j hj
    cases p with
    | inl val => contradiction
    | inr val =>
      simp only [Bounded] at h1 h2
      simp only [cook, Pointer.node.injEq] at hj
      rw [Fin.eq_mk_iff_val_eq] at hj
      simp only at hj
      subst hj
      use ⟨j.1, h2 rfl⟩
      simp [RawPointer.cook]
end RawPointer
end RawBdd
