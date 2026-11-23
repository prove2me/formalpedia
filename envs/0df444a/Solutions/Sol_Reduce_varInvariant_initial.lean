-- Prove2me | solution 1 for Reduce.varInvariant_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:07:32.756807+00:00
-- url     : https://prove2.me/submissions/0a6b6077-7470-49ac-b7e4-563b09fad169

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
theorem _root_.solution {n m : Nat} {O : OBdd n m} :
    VarInvariant O (provedStateInitial n m) := by
  intro j k
  exact absurd k.isLt (by simp [provedStateInitial])
end Reduce
