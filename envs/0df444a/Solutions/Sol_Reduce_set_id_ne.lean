-- Prove2me | solution 1 for Reduce.set_id_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:01:22.810116+00:00
-- url     : https://prove2.me/submissions/d6483b28-2c97-4ca5-b6b3-841007f93545

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State

set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution {n m : Nat} (ps : ProvedState n m) (j k : Fin m) (p : RawPointer)
    (h : k ≠ j) : (set_id ps j p).state.ids[k] = ps.state.ids[k] := by
  show (ps.state.ids.set j (some p))[k] = ps.state.ids[k]
  exact Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne h.symm)
end Reduce
