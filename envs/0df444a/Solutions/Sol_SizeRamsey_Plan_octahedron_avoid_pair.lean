-- Prove2me | solution 1 for SizeRamsey.Plan.octahedron_avoid_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:31.486821+00:00
-- url     : https://prove2.me/submissions/c29fa67d-2a49-4032-a33b-a5db3fc65fd4

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
theorem _root_.solution : ∀ x y : Fin 6, ∃ a b c d : Fin 6, octahedron.Adj a b ∧
    octahedron.Adj b c ∧ octahedron.Adj c d ∧ octahedron.Adj d a ∧ a ≠ c ∧ b ≠ d ∧
    a ≠ x ∧ b ≠ x ∧ c ≠ x ∧ d ≠ x ∧ a ≠ y ∧ b ≠ y ∧ c ≠ y ∧ d ≠ y := by
  decide
end SizeRamsey.Plan
