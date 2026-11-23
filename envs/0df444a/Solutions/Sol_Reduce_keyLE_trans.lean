-- Prove2me | solution 1 for Reduce.keyLE_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:06:35.842963+00:00
-- url     : https://prove2.me/submissions/3405237a-4f28-4aa6-ba22-8ff56ab6f115

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
import Theorems.Thm_Reduce_rawPointer_le_refl
import Theorems.Thm_Reduce_rawPointer_le_trans
import Theorems.Thm_Reduce_rawPointer_le_antisymm

set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution {a b c : RawPointer × RawPointer} : KeyLE a b → KeyLE b c → KeyLE a c := by
  unfold KeyLE leKeyPair
  intro hab hbc
  by_cases h1 : a.1 = b.1 <;> by_cases h2 : b.1 = c.1
  · -- a.1 = b.1 and b.1 = c.1
    have h13 : a.1 = c.1 := h1.trans h2
    rw [if_pos h1] at hab
    rw [if_pos h2] at hbc
    rw [if_pos h13]
    exact decide_eq_true
      (rawPointer_le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  · -- a.1 = b.1 and b.1 ≠ c.1
    have h13 : a.1 ≠ c.1 := h1 ▸ h2
    rw [if_neg h2] at hbc
    rw [if_neg h13]
    rw [h1]
    exact hbc
  · -- a.1 ≠ b.1 and b.1 = c.1
    have h13 : a.1 ≠ c.1 := h2 ▸ h1
    rw [if_neg h1] at hab
    rw [if_neg h13]
    rw [← h2]
    exact hab
  · -- a.1 ≠ b.1 and b.1 ≠ c.1
    rw [if_neg h1] at hab
    rw [if_neg h2] at hbc
    have hac : a.1 ≤ c.1 :=
      rawPointer_le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)
    have h13 : a.1 ≠ c.1 := by
      intro he
      have hca : c.1 ≤ a.1 := he ▸ rawPointer_le_refl a.1
      have hba : b.1 ≤ a.1 := rawPointer_le_trans (of_decide_eq_true hbc) hca
      exact h1 (rawPointer_le_antisymm (of_decide_eq_true hab) hba)
    rw [if_neg h13]
    exact decide_eq_true hac
end Reduce
