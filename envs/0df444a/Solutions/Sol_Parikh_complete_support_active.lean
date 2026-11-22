-- Prove2me | solution 1 for Parikh.complete_support_active
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:15.563982+00:00
-- url     : https://prove2.me/submissions/3036904a-8900-441c-aaa7-e60eb0ca7346

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Theorems.Thm_Parikh_Valid_support_active

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution (g : ContextFreeGrammar T) (t : ParseTree T g.NT)
    (ht : Complete g t) : t.support ⊆ (activeNonterminals g : Set g.NT) := by
  exact ht.1.support_active
end Parikh
