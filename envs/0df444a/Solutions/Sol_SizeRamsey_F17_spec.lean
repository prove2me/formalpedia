-- Prove2me | solution 1 for SizeRamsey.F17_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:32:55.878+00:00
-- url     : https://prove2.me/submissions/a43100a8-cd34-4d48-9ee1-104c51a269df

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SizeRamsey
public import Definitions.Def_SizeRamsey_Solution
public import Theorems.Thm_SizeRamsey_Proof_F17_spec


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution : F17.Connected ∧ edgeCount F17 = 17 ∧ ArrowsMatching4C4 F17 := by
  exact Proof.F17_spec
end SizeRamsey
