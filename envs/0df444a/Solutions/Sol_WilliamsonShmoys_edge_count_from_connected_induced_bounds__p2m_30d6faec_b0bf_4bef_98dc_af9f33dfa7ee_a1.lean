-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_from_connected_induced_bounds__p2m_30d6faec_b0bf_4bef_98dc_af9f33dfa7ee_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:37:28.483815+00:00
-- url     : https://prove2.me/submissions/296557a7-6240-4d4b-913a-5ada15f626bf

import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_connected_finset_bounds__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) (H : SimpleGraph V)
    (hconnBound : ∀ s : Finset V, 3 ≤ s.card →
      (H.induce (↑s : Set V)).Connected →
      letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
      (H.induce (↑s : Set V)).edgeFinset.card ≤ 3 * s.card - 6) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  have hcomp : ∀ s : Finset V, 3 ≤ s.card →
      (H.induce (↑s : Set V)).Connected →
      (H.induce (↑s : Set V)).edgeSet.ncard + 6 ≤ 3 * s.card := by
    intro s hs hconnected
    have hb := hconnBound s hs hconnected
    have he : (H.induce (↑s : Set V)).edgeSet.ncard =
        (H.induce (↑s : Set V)).edgeFinset.card := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    rw [he]
    omega
  have h :=
    WilliamsonShmoys.planar_edge_bound_from_connected_finset_bounds__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
      H hcard hcomp
  have he : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [he] at h
  omega
