-- Prove2me | solution 1 for SizeRamsey.Plan.small_degrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:33.716702+00:00
-- url     : https://prove2.me/submissions/4d1e24cf-acb5-4d13-b36f-2a92d219bf0a

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Theorems.Thm_SizeRamsey_Plan_small_degrees_comp

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution :
    (∀ i : Fin 4, (SimpleGraph.cycleGraph 4).degree i = 2) ∧
    (∀ i : Fin 5,
      wheel5.degree i = if i = 4 then 4 else 3) ∧
    (∀ i : Fin 6,
      k33MinusEdge.degree i =
        if i = 0 ∨ i = 3 then 2 else 3) ∧
    (∀ i : Fin 6, octahedron.degree i = 4) := by
  convert small_degrees_comp using 0
end SizeRamsey.Plan
