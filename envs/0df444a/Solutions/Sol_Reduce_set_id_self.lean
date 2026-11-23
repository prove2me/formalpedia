-- Prove2me | solution 1 for Reduce.set_id_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:01:22.223831+00:00
-- url     : https://prove2.me/submissions/5a694963-c4c6-4077-9254-319762cf1be1

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
theorem _root_.solution {n m : Nat} (ps : ProvedState n m) (j : Fin m) (p : RawPointer) :
    (set_id ps j p).state.ids[j] = some p := by
  show (ps.state.ids.set j (some p))[j] = some p
  simp [Vector.getElem_set_self]
end Reduce
