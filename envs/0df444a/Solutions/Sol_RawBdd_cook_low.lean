-- Prove2me | solution 1 for RawBdd.cook_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:59:12.809276+00:00
-- url     : https://prove2.me/submissions/4bef7190-d516-4eca-b494-7db4bcbcd0eb

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic

set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
open RawBdd
namespace RawBdd
theorem _root_.solution {rn : RawNode n} {h1} {h2} : rn.lo.cook (m := m) h1 = (rn.cook h2).low := rfl
end RawBdd
