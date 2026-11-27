-- Prove2me | solution 1 for SizeRamsey.Plan.small_degrees_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:56.458908+00:00
-- url     : https://prove2.me/submissions/726bdd1c-57fc-4c09-8893-057b4358936d

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
theorem _root_.solution :
    (∀ i : Fin 4, (SimpleGraph.cycleGraph 4).degree i = 2) ∧
    (∀ i : Fin 5,
      wheel5.degree i = if i = 4 then 4 else 3) ∧
    (∀ i : Fin 6,
      k33MinusEdge.degree i =
        if i = 0 ∨ i = 3 then 2 else 3) ∧
    (∀ i : Fin 6, octahedron.degree i = 4) := by
  decide
end SizeRamsey.Plan
