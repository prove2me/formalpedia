-- Prove2me | solution 1 for Reduce.keyLE_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:06:13.169987+00:00
-- url     : https://prove2.me/submissions/c2d6233a-8e47-4679-aaa5-bc7e0ab0df74

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
import Theorems.Thm_Reduce_rawPointer_le_antisymm

set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution {a b : RawPointer × RawPointer} : KeyLE a b → KeyLE b a → a = b := by
  unfold KeyLE leKeyPair
  by_cases h1 : a.1 = b.1
  · rw [if_pos h1, if_pos h1.symm]
    intro hab hba
    exact Prod.ext h1 (rawPointer_le_antisymm (of_decide_eq_true hab) (of_decide_eq_true hba))
  · rw [if_neg h1, if_neg (Ne.symm h1)]
    intro hab hba
    exact absurd (rawPointer_le_antisymm (of_decide_eq_true hab) (of_decide_eq_true hba)) h1
end Reduce
