-- Prove2me | solution 1 for Parikh.EncodedGrammar.compile_bit_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:56:25.557867+00:00
-- url     : https://prove2.me/submissions/c4de70e0-9bed-4404-9293-8cd83eb7586f

module
public import Definitions.Def_LeanPool_Parikh_CompilerTrees
public import Definitions.Def_LeanPool_Parikh_CompilerBounds
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Theorems.Thm_Parikh_witness_bit_bound


set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar
namespace Parikh.EncodedGrammar
theorem _root_.solution (g : EncodedGrammar) :
    entryBits g.size g.compile ≤ g.size.vectorBits ∧
      (∀ c ∈ g.compile, ∀ a, c.base a < 2 ^ g.size.coordinateBits) ∧
      (∀ c ∈ g.compile, ∀ p ∈ c.periods, ∀ a, p a < 2 ^ g.size.coordinateBits) :=
  witness_bit_bound g.size (by simp [size]) g.compile g.compile_bounded
end Parikh.EncodedGrammar
