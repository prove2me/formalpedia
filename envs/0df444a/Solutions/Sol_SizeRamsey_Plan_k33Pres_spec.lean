-- Prove2me | solution 1 for SizeRamsey.Plan.k33Pres_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:23.675801+00:00
-- url     : https://prove2.me/submissions/cc6c871b-efc3-4c20-895e-24e44ab2afd3

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
theorem _root_.solution : ∀ v, v ∈ k33Pres v ∧ (k33Pres v).card = 2 ∧
    QTrans k33MinusEdge (k33Pres v) := by
  decide
end SizeRamsey.Plan
