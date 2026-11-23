-- Prove2me | solution 1 for Reduce.keyLE_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:06:06.306303+00:00
-- url     : https://prove2.me/submissions/83b1405d-8041-41ad-b221-be6761e4eb65

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
import Theorems.Thm_Reduce_rawPointer_le_refl

set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution (a : RawPointer × RawPointer) : KeyLE a a := by
  unfold KeyLE leKeyPair
  rw [if_pos rfl]
  exact decide_eq_true (rawPointer_le_refl a.2)
end Reduce
