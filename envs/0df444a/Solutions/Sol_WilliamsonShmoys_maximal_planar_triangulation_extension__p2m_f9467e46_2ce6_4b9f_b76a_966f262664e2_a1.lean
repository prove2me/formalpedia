-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_f9467e46_2ce6_4b9f_b76a_966f262664e2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:59:07.436985+00:00
-- url     : https://prove2.me/submissions/452112ac-7efc-44a9-a26c-b68a54b60fad

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_3a18cd50_a833_4853_9055_3e93726fc3e4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_3a18cd50_a833_4853_9055_3e93726fc3e4_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨M, hGM, hM, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_3a18cd50_a833_4853_9055_3e93726fc3e4_a1 G hG
  exact ⟨M, hGM, hM,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_3a18cd50_a833_4853_9055_3e93726fc3e4_a1 M hM hMax hCard⟩