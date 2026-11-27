-- Prove2me | solution 1 for SizeRamsey.Plan.wheel5_edgeCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:58.314817+00:00
-- url     : https://prove2.me/submissions/6501e4a4-8663-409e-ad98-f720106fa9e9

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
theorem _root_.solution : edgeCount wheel5 = 8 := by
  rw [edgeCount_eq_card]; decide
end SizeRamsey.Plan
