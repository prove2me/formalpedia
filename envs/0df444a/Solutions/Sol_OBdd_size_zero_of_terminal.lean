-- Prove2me | solution 1 for OBdd.size_zero_of_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:51.308445+00:00
-- url     : https://prove2.me/submissions/9bf0f0e8-fd3b-49ce-b34f-fb123964356b

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
namespace OBdd
theorem _root_.solution : OBdd.isTerminal O → O.size' = 0 := by
  rintro ⟨b, h⟩
  rcases O with ⟨⟨heap, root⟩, o⟩
  subst h
  exact congrArg DecisionTree.size (OBdd.toTree_terminal (h := o))
end OBdd
