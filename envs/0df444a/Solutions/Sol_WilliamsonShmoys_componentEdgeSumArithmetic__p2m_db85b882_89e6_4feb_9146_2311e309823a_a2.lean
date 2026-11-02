-- Prove2me | solution 1 for WilliamsonShmoys.componentEdgeSumArithmetic__p2m_db85b882_89e6_4feb_9146_2311e309823a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:27:40.563764+00:00
-- url     : https://prove2.me/submissions/3a1f3d9d-16c5-40e9-9b0a-ec1719f91645

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (C : Finset (Finset V)) (edgeCount : Finset V → Nat) (edgeTotal : Nat)
    (hCcard : 2 ≤ C.card)
    (hVertexSum : (∑ s ∈ C, s.card) = Fintype.card V)
    (hEdgeSum : (∑ s ∈ C, edgeCount s) = edgeTotal)
    (hComponentBound : ∀ s ∈ C, edgeCount s + 3 ≤ 3 * s.card)
    (hn : 3 ≤ Fintype.card V) :
    edgeTotal ≤ 3 * Fintype.card V - 6 := by
  have hsum := Finset.sum_le_sum hComponentBound
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  rw [hEdgeSum] at hsum
  have htotal : edgeTotal + C.card * 3 ≤ 3 * Fintype.card V := by
    calc
      edgeTotal + C.card * 3 ≤ ∑ s ∈ C, 3 * s.card := hsum
      _ = 3 * (∑ s ∈ C, s.card) := by rw [← Finset.mul_sum]
      _ = 3 * Fintype.card V := by rw [hVertexSum]
  omega