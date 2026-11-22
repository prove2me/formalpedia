-- Prove2me | solution 1 for Parikh.parikhImage_isSemilinear_of_grammar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:57:02.871671+00:00
-- url     : https://prove2.me/submissions/2fe2758b-54a2-43d2-b7e8-c8dbb0238559

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
public import Theorems.Thm_Parikh_grammar_image


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} [Finite T] [DecidableEq T]
    (g : ContextFreeGrammar T) : IsSemilinearSet (parikhImage g.language) := grammar_image g
end Parikh
