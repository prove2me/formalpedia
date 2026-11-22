-- Prove2me | solution 1 for Parikh.exists_boundedSemilinearRepresentation_of_grammar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:57:09.042169+00:00
-- url     : https://prove2.me/submissions/1b95905d-273f-40d6-b53c-a268ab6d8a13

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
public import Theorems.Thm_Parikh_bounded_witness


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*}
    [Fintype T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ W : SemilinearRepresentation T,
      W.denotation = parikhImage g.language ∧ WithinBounds (grammarSize g) W := bounded_witness g
end Parikh
