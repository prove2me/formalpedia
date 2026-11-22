-- Prove2me | solution 1 for Parikh.compileGrammar_bit_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:57:35.186901+00:00
-- url     : https://prove2.me/submissions/6b19fa0e-7119-4ace-a2b2-434eaa0839af

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
public import Theorems.Thm_Parikh_EncodedGrammar_compile_bit_bound


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution (g : EncodedGrammar) :
    entryBits g.size (compileGrammar g) ≤ g.size.vectorBits ∧
      (∀ c ∈ compileGrammar g, ∀ a, c.base a < 2 ^ g.size.coordinateBits) ∧
      (∀ c ∈ compileGrammar g, ∀ p ∈ c.periods, ∀ a, p a < 2 ^ g.size.coordinateBits) :=
  g.compile_bit_bound
end Parikh
