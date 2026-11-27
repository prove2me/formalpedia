-- Prove2me | solution 1 for SizeRamsey.Plan.octahedronPres_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:26.717434+00:00
-- url     : https://prove2.me/submissions/628199b1-68d8-4da2-a7d8-aabfd303e0d8

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
theorem _root_.solution : ∀ v, v ∈ octahedronPres v ∧ (octahedronPres v).card = 3 ∧
    QTrans octahedron (octahedronPres v) := by
  decide
end SizeRamsey.Plan
