-- Prove2me | solution 1 for Reduce.rawPointer_le_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:05:59.742559+00:00
-- url     : https://prove2.me/submissions/821c2b69-721e-4d0c-86b5-410bbef8ae71

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
theorem _root_.solution {a b c : RawPointer} : a ≤ b → b ≤ c → a ≤ c := le_trans
end Reduce
