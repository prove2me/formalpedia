-- Prove2me | solution 1 for SizeRamsey.Plan.cycle4Pres_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:05.637936+00:00
-- url     : https://prove2.me/submissions/4301199e-5d09-43fb-b008-59567daf20d3

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
theorem _root_.solution : ∀ v, v ∈ cycle4Pres v ∧ (cycle4Pres v).card = 1 ∧
    QTrans (SimpleGraph.cycleGraph 4) (cycle4Pres v) := by
  decide
end SizeRamsey.Plan
