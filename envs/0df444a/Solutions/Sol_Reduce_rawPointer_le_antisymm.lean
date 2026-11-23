-- Prove2me | solution 1 for Reduce.rawPointer_le_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:01:04.749522+00:00
-- url     : https://prove2.me/submissions/ddfe9f1a-2e57-44a9-9452-5069b6925dfc

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
theorem _root_.solution {a b : RawPointer} : a ≤ b → b ≤ a → a = b := le_antisymm
end Reduce
