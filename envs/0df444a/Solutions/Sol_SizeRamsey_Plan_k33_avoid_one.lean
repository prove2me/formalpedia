-- Prove2me | solution 1 for SizeRamsey.Plan.k33_avoid_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:30.980367+00:00
-- url     : https://prove2.me/submissions/1a0f2240-a7aa-4dc9-b6a7-3830816b3252

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
namespace SizeRamsey.Plan
theorem _root_.solution : ∀ x : Fin 6, ∃ a b c d : Fin 6, k33MinusEdge.Adj a b ∧
    k33MinusEdge.Adj b c ∧ k33MinusEdge.Adj c d ∧ k33MinusEdge.Adj d a ∧ a ≠ c ∧ b ≠ d ∧
    a ≠ x ∧ b ≠ x ∧ c ≠ x ∧ d ≠ x := by
  decide
end SizeRamsey.Plan
