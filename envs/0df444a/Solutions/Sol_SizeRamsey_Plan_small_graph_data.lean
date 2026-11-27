-- Prove2me | solution 1 for SizeRamsey.Plan.small_graph_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:57.456468+00:00
-- url     : https://prove2.me/submissions/dbe0af02-4858-4eb8-a81a-45fd667daf2f

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Theorems.Thm_SizeRamsey_Plan_cycle4_edgeCount
public import Theorems.Thm_SizeRamsey_Plan_wheel5_edgeCount
public import Theorems.Thm_SizeRamsey_Plan_k33MinusEdge_edgeCount
public import Theorems.Thm_SizeRamsey_Plan_octahedron_edgeCount
public import Theorems.Thm_SizeRamsey_Plan_cycle4_tau
public import Theorems.Thm_SizeRamsey_Plan_wheel5_tau
public import Theorems.Thm_SizeRamsey_Plan_k33_tau
public import Theorems.Thm_SizeRamsey_Plan_octahedron_tau

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution :
    (edgeCount (SimpleGraph.cycleGraph 4) = 4 ∧
      tau4 (SimpleGraph.cycleGraph 4) = 1 ∧
      PrescribedOptimal (SimpleGraph.cycleGraph 4)) ∧
    (edgeCount wheel5 = 8 ∧ tau4 wheel5 = 2 ∧
      PrescribedOptimal wheel5) ∧
    (edgeCount k33MinusEdge = 8 ∧ tau4 k33MinusEdge = 2 ∧
      PrescribedOptimal k33MinusEdge) ∧
    (edgeCount octahedron = 12 ∧ tau4 octahedron = 3 ∧
      PrescribedOptimal octahedron) :=
  ⟨⟨cycle4_edgeCount, cycle4_tau⟩, ⟨wheel5_edgeCount, wheel5_tau⟩,
    ⟨k33MinusEdge_edgeCount, k33_tau⟩, ⟨octahedron_edgeCount, octahedron_tau⟩⟩
end SizeRamsey.Plan
