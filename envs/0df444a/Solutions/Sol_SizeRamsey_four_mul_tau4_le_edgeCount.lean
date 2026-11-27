-- Prove2me | solution 1 for SizeRamsey.four_mul_tau4_le_edgeCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:32:10.658573+00:00
-- url     : https://prove2.me/submissions/cec553de-b550-4ec4-9e31-e72dc60dcd83

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SizeRamsey
public import Definitions.Def_SizeRamsey_Solution
public import Theorems.Thm_SizeRamsey_Proof_four_mul_tau4_le_edgeCount


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution {n : ℕ} (G : SimpleGraph (Fin n)) :
    4 * tau4 G ≤ edgeCount G := by
  exact Proof.four_mul_tau4_le_edgeCount G
end SizeRamsey
