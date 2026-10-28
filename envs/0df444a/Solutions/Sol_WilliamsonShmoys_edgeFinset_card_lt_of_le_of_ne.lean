-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_lt_of_le_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:12:02.377644+00:00
-- url     : https://prove2.me/submissions/5822358c-ea45-429b-b8ad-2b575db2c2ab

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    {G H : SimpleGraph V}
    (hGFinite : Fintype G.edgeSet)
    (hHFinite : Fintype H.edgeSet)
    (hGH : G ≤ H)
    (hne : H ≠ G) :
    G.edgeFinset.card < H.edgeFinset.card := by
  letI := hGFinite
  letI := hHFinite
  apply Finset.card_lt_card
  rw [SimpleGraph.edgeFinset_ssubset_edgeFinset]
  exact lt_of_le_of_ne hGH (Ne.symm hne)