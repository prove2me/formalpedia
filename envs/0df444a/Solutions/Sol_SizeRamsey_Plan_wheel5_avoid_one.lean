-- Prove2me | solution 1 for SizeRamsey.Plan.wheel5_avoid_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:30.514871+00:00
-- url     : https://prove2.me/submissions/0af5ff50-21ed-4149-92d1-2094bdfcc411

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
theorem _root_.solution : ∀ x : Fin 5, ∃ a b c d : Fin 5, wheel5.Adj a b ∧ wheel5.Adj b c ∧
    wheel5.Adj c d ∧ wheel5.Adj d a ∧ a ≠ c ∧ b ≠ d ∧ a ≠ x ∧ b ≠ x ∧ c ≠ x ∧ d ≠ x := by
  decide
end SizeRamsey.Plan
