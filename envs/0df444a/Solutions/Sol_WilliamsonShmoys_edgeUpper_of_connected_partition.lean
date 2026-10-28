-- Prove2me | solution 1 for WilliamsonShmoys.edgeUpper_of_connected_partition
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:09:12.203349+00:00
-- url     : https://prove2.me/submissions/dcce26b5-c308-425b-bf64-aafd2a034624

import Mathlib
import Theorems.Thm_WilliamsonShmoys_edge_ncard_eq_sum_induce
import Theorems.Thm_WilliamsonShmoys_card_sum_of_partition
import Theorems.Thm_WilliamsonShmoys_connected_piece_nonempty
import Theorems.Thm_WilliamsonShmoys_connected_small_piece_edge_bound
import Theorems.Thm_WilliamsonShmoys_aggregate_piece_edge_bounds

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (C : Finset (Finset V))
    (connectedInducedBound : ∀ (S : Finset V),
      (G.induce (↑S : Set V)).Connected →
      3 ≤ Fintype.card S →
      (G.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * Fintype.card S)
    (hV : 3 ≤ Fintype.card V)
    (hcover : ∀ v : V, ∃ S, S ∈ C ∧ v ∈ S)
    (hdisjoint : ∀ S, S ∈ C → ∀ T, T ∈ C → S ≠ T → Disjoint S T)
    (hconnected : ∀ S, S ∈ C → (G.induce (↑S : Set V)).Connected)
    (hadj : ∀ ⦃u v : V⦄, G.Adj u v → ∃ S, S ∈ C ∧ u ∈ S ∧ v ∈ S) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  let e : Finset V → Nat :=
    fun S => (G.induce (↑S : Set V)).edgeSet.ncard
  have hsumE :
      G.edgeSet.ncard = ∑ S ∈ C, e S :=
    WilliamsonShmoys.edge_ncard_eq_sum_induce G C hcover hdisjoint hadj
  have hsumV : (∑ S ∈ C, S.card) = Fintype.card V :=
    WilliamsonShmoys.card_sum_of_partition C hcover hdisjoint
  have hne : ∀ S, S ∈ C → 0 < S.card := by
    intro S hS
    exact WilliamsonShmoys.connected_piece_nonempty G S (hconnected S hS)
  have hsmall : ∀ S, S ∈ C → 0 < S.card → S.card < 3 →
      e S + 3 ≤ 3 * S.card := by
    intro S hS hpos hlt
    exact WilliamsonShmoys.connected_small_piece_edge_bound
      G S (hconnected S hS) hpos hlt
  have hlarge : ∀ S, S ∈ C → 3 ≤ S.card →
      e S + 6 ≤ 3 * S.card := by
    intro S hS hlarge
    have hlargeSub : 3 ≤ Fintype.card S := by simpa using hlarge
    simpa [e] using connectedInducedBound S (hconnected S hS) hlargeSub
  have hsum := WilliamsonShmoys.aggregate_piece_edge_bounds
    C e hV hsumV hne hsmall hlarge
  calc
    G.edgeSet.ncard + 6 = (∑ S ∈ C, e S) + 6 := by rw [hsumE]
    _ ≤ 3 * (∑ S ∈ C, S.card) := hsum
    _ = 3 * Fintype.card V := by rw [hsumV]
