-- Prove2me | solution 1 for Parikh.compileGrammar_size_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:57:14.490804+00:00
-- url     : https://prove2.me/submissions/beb9e9e4-3d31-4de3-81db-221b6e18ca5e

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
    WithinBounds g.size (compileGrammar g) := compiler.bounded g
end Parikh
