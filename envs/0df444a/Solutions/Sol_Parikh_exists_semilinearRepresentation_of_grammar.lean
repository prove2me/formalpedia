-- Prove2me | solution 1 for Parikh.exists_semilinearRepresentation_of_grammar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:57:06.221665+00:00
-- url     : https://prove2.me/submissions/5efe9fb5-8351-448c-8feb-d88c94952423

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
public import Theorems.Thm_Parikh_grammar_witness


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} [Finite T] [DecidableEq T]
    (g : ContextFreeGrammar T) :
    ∃ W : SemilinearRepresentation T, W.denotation = parikhImage g.language := grammar_witness g
end Parikh
