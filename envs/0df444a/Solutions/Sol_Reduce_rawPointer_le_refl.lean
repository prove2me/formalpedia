-- Prove2me | solution 1 for Reduce.rawPointer_le_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:00:57.020803+00:00
-- url     : https://prove2.me/submissions/1060821c-3af2-45da-b415-29c0216cefca

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
theorem _root_.solution (a : RawPointer) : a ≤ a := le_refl a
end Reduce
