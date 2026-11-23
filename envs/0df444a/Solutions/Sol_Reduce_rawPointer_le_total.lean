-- Prove2me | solution 1 for Reduce.rawPointer_le_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:05:57.151981+00:00
-- url     : https://prove2.me/submissions/cf53602d-5dec-4f3c-8ff7-59c88946c9f6

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
theorem _root_.solution (a b : RawPointer) : a ≤ b ∨ b ≤ a := le_total a b
end Reduce
