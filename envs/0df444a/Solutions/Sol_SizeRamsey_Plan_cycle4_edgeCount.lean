-- Prove2me | solution 1 for SizeRamsey.Plan.cycle4_edgeCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:38.311996+00:00
-- url     : https://prove2.me/submissions/10dff337-8b0b-49f3-9d79-a4dd271e7eb4

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Theorems.Thm_SizeRamsey_edgeCount_eq_card


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
namespace SizeRamsey.Plan
theorem _root_.solution : edgeCount (SimpleGraph.cycleGraph 4) = 4 := by
  rw [edgeCount_eq_card]; decide
end SizeRamsey.Plan
