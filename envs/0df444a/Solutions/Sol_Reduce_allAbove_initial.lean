-- Prove2me | solution 1 for Reduce.allAbove_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:08:28.262381+00:00
-- url     : https://prove2.me/submissions/b2e740ec-88e0-4460-898f-cb7a47f9a05d

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
theorem _root_.solution {n m : Nat} {i : Nat} :
    AllAbove (provedStateInitial n m) i := by
  intro k
  exact absurd k.isLt (by simp [provedStateInitial])
end Reduce
