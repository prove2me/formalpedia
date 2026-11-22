-- Prove2me | solution 1 for Parikh.regular_realization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:56:39.242874+00:00
-- url     : https://prove2.me/submissions/501ff1a7-ac82-4027-9a78-b6d9253b7857

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Theorems.Thm_Parikh_grammar_image
public import Theorems.Thm_Parikh_converse


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ R : Language T, R.IsRegular ∧ image R = image g.language := by
  exact converse (image g.language) (grammar_image g)
end Parikh
