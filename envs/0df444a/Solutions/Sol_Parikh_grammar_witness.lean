-- Prove2me | solution 1 for Parikh.grammar_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:55:02.72744+00:00
-- url     : https://prove2.me/submissions/cb9dd972-6161-42f3-93f1-2b4f555ae9d5

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Theorems.Thm_Parikh_grammar_image
public import Theorems.Thm_Parikh_exists_witness


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ W : Witness T, W.denotation = image g.language := by
  exact exists_witness (image g.language) (grammar_image g)
end Parikh
