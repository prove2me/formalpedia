-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_below_planar_bound_has_drawable_strict_supergraph__p2m_b704201f_fc6b_4e4c_b576_9e83647d88b7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:19:26.392193+00:00
-- url     : https://prove2.me/submissions/f93a0805-f65d-4bad-8cab-b5afd7f55867

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists__p2m_957d5f50_de1a_483c_adf7_e58da3f91888_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_957d5f50_de1a_483c_adf7_e58da3f91888_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hEdges : K.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ L : SimpleGraph V, K < L ∧ HasPlanarDrawingOn L := by
  obtain ⟨M, hKM, hMPlanar, hMmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_957d5f50_de1a_483c_adf7_e58da3f91888_a1 K hK
  have hMEdges :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_957d5f50_de1a_483c_adf7_e58da3f91888_a1
      M hMPlanar hCard hMmax
  have hKneM : K ≠ M := by
    intro hEq
    subst M
    exact (Nat.ne_of_lt hEdges) hMEdges
  exact ⟨M, lt_of_le_of_ne hKM hKneM, hMPlanar⟩