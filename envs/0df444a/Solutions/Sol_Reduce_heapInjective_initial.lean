-- Prove2me | solution 1 for Reduce.heapInjective_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:08:30.813395+00:00
-- url     : https://prove2.me/submissions/83270ca4-15f8-4c31-bc7f-6e107eed0215

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution {n m : Nat} :
    HeapInjective (provedStateInitial n m) := by
  intro k1
  exact absurd k1.isLt (by simp [provedStateInitial])
end Reduce
