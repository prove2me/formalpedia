-- Prove2me | solution 1 for SizeRamsey.Plan.k33MinusEdge_edgeCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:01.244299+00:00
-- url     : https://prove2.me/submissions/ee603759-966d-4fbb-98a1-2bef27974546

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
theorem _root_.solution : edgeCount k33MinusEdge = 8 := by
  rw [edgeCount_eq_card]; decide
end SizeRamsey.Plan
