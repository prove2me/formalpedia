-- Prove2me | solution 1 for Parikh.compileGrammar_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:57:10.005825+00:00
-- url     : https://prove2.me/submissions/d0f4dd6f-5bea-4dc0-823e-b1c80c70d338

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api

set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution (g : EncodedGrammar) :
    (compileGrammar g).denotation = parikhImage g.decode.language := compiler.correct g
end Parikh
