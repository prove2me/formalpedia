-- Prove2me | solution 1 for SizeRamsey.avoiding_coloring_le_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:41:37.772163+00:00
-- url     : https://prove2.me/submissions/23dde7c3-32a4-4885-be6b-64ab51a24961

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SizeRamsey
public import Definitions.Def_SizeRamsey_Solution
public import Theorems.Thm_SizeRamsey_Proof_avoiding_coloring_le_sixteen


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution {n : ℕ} (F : SimpleGraph (Fin n))
    (hconn : F.Connected) (hle : edgeCount F ≤ 16) :
    ∃ R : SimpleGraph (Fin n), R ≤ F ∧ ¬ HasMatching4 R ∧ ¬ HasC4 (F \ R) := by
  exact Proof.avoiding_coloring_le_sixteen F hconn hle
end SizeRamsey
