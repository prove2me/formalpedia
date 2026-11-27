-- Prove2me | solution 1 for SizeRamsey.equality_classification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:39:31.213965+00:00
-- url     : https://prove2.me/submissions/1ddd62b9-18ce-47b4-8f89-f9014dd592f4

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SizeRamsey
public import Definitions.Def_SizeRamsey_Solution
public import Theorems.Thm_SizeRamsey_Proof_equality_classification


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution {n : ℕ} (G : SimpleGraph (Fin n))
    (hconn : G.Connected) (hpos : 0 < edgeCount G) (hle : edgeCount G ≤ 16) :
    4 * tau4 G = edgeCount G ↔
      Nonempty (G ≃g SimpleGraph.cycleGraph 4) ∨ Nonempty (G ≃g wheel5) ∨
      Nonempty (G ≃g k33MinusEdge) ∨ Nonempty (G ≃g octahedron) := by
  exact Proof.equality_classification G hconn hpos hle
end SizeRamsey
