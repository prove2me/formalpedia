-- Prove2me | solution 1 for SizeRamsey.Plan.octahedron_edgeCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:03.062197+00:00
-- url     : https://prove2.me/submissions/2257a1fe-0cfd-493d-9c89-49208c5766f4

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
theorem _root_.solution : edgeCount octahedron = 12 := by
  rw [edgeCount_eq_card]; decide
end SizeRamsey.Plan
