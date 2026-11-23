-- Prove2me | solution 1 for OBdd.card_relevantPointer_eq_one_of_isTerminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:20.485804+00:00
-- url     : https://prove2.me/submissions/fe526f19-98fa-4afe-b38f-892c45940c47

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_Bdd_terminal_relevant_iff

set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} : O.isTerminal → Fintype.card O.1.RelevantPointer = 1 := by
  intro h
  refine Fintype.card_eq_one_iff.mpr ?_
  rcases h with ⟨b, hb⟩
  use ⟨terminal b, by rw [hb]; left⟩
  intro y
  apply Subtype.ext_iff.mpr
  apply (terminal_relevant_iff hb y).mp
  rfl
end OBdd
