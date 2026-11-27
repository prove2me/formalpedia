-- Prove2me | solution 1 for SizeRamsey.connectedSizeRamsey_eq_seventeen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:42:21.855842+00:00
-- url     : https://prove2.me/submissions/a8dde70e-47cc-4252-b9ab-d5cdf46e313f

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SizeRamsey
public import Definitions.Def_SizeRamsey_Solution
public import Theorems.Thm_SizeRamsey_avoiding_coloring_le_sixteen
public import Theorems.Thm_SizeRamsey_F17_spec
public import Theorems.Thm_SizeRamsey_Proof_F17_spec
public import Theorems.Thm_SizeRamsey_Proof_avoiding_coloring_le_sixteen


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution : connectedSizeRamsey = 17 := by
  have hmem : 17 ∈ {m : ℕ | ∃ (n : ℕ) (F : SimpleGraph (Fin n)),
      F.Connected ∧ edgeCount F = m ∧ ArrowsMatching4C4 F} :=
    ⟨12, F17, F17_spec⟩
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨17, hmem⟩
  intro m hm
  rcases hm with ⟨n, F, hconn, hcount, harr⟩
  by_contra h
  have hm16 : m ≤ 16 := Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
  obtain ⟨R, hRF, hR, hB⟩ := avoiding_coloring_le_sixteen F hconn (hcount ▸ hm16)
  exact (harr R hRF).elim hR hB
end SizeRamsey
