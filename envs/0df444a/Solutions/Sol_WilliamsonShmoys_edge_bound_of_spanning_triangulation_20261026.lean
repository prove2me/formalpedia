-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_spanning_triangulation_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:20:47.054076+00:00
-- url     : https://prove2.me/submissions/8594ee4a-5ea0-43ee-8452-f45b09c04c3a

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (H : SimpleGraph V)
    (hsub : ∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v)
    (hcard : H.edgeSet.ncard = 3 * Fintype.card V - 6) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  have hKH : K ≤ H := (SimpleGraph.le_iff_adj).2 fun u v huv => hsub huv
  calc
    K.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono (SimpleGraph.edgeSet_mono hKH)
    _ = 3 * Fintype.card V - 6 := hcard