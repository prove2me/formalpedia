-- Prove2me | solution 1 for Parikh.card_treeLeaves_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:10.017797+00:00
-- url     : https://prove2.me/submissions/6786533a-48c4-4851-9430-396c19468e5b

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} [Fintype T]
namespace Parikh
theorem _root_.solution (g : ContextFreeGrammar T) :
    (treeLeaves g).card ≤ Fintype.card T + (activeNonterminals g).card := by
  classical
  apply (Finset.card_union_le _ _).trans
  exact Nat.add_le_add (by simpa using Finset.card_image_le (s := (Finset.univ : Finset T)))
    Finset.card_image_le
end Parikh
