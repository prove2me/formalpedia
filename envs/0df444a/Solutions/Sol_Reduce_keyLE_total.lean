-- Prove2me | solution 1 for Reduce.keyLE_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:06:32.976472+00:00
-- url     : https://prove2.me/submissions/871c1be1-f9cc-4cef-9b14-a1a7d9367104

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
import Theorems.Thm_Reduce_rawPointer_le_total

set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution (a b : RawPointer × RawPointer) : KeyLE a b ∨ KeyLE b a := by
  unfold KeyLE leKeyPair
  by_cases h1 : a.1 = b.1
  · rw [if_pos h1, if_pos h1.symm]
    rcases rawPointer_le_total a.2 b.2 with h | h
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (decide_eq_true h)
  · rw [if_neg h1, if_neg (Ne.symm h1)]
    rcases rawPointer_le_total a.1 b.1 with h | h
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (decide_eq_true h)
end Reduce
