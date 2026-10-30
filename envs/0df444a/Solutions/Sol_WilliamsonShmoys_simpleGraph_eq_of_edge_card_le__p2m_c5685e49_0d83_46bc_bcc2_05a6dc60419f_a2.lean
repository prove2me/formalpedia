-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_eq_of_edge_card_le__p2m_c5685e49_0d83_46bc_bcc2_05a6dc60419f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:27:02.427689+00:00
-- url     : https://prove2.me/submissions/9b5baf9e-209d-4ca6-9461-503070d103dc

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hcard : Nat.card {e : Sym2 V // e ∈ H.edgeSet} ≤
      Nat.card {e : Sym2 V // e ∈ G.edgeSet}) : H = G := by
  classical
  have hcard' : Fintype.card H.edgeSet ≤ Fintype.card G.edgeSet := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hedge : G.edgeSet = H.edgeSet :=
    Set.eq_of_subset_of_card_le (SimpleGraph.edgeSet_mono hGH) hcard'
  exact (SimpleGraph.edgeSet_inj).mp hedge.symm