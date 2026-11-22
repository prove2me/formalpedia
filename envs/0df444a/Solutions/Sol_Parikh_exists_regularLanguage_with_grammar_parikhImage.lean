-- Prove2me | solution 1 for Parikh.exists_regularLanguage_with_grammar_parikhImage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:57:20.494557+00:00
-- url     : https://prove2.me/submissions/760b2226-09a4-4595-9170-d83cdb567e89

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
public import Theorems.Thm_Parikh_regular_realization


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*}
    [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ R : Language T, R.IsRegular ∧ parikhImage R = parikhImage g.language := regular_realization g
end Parikh
