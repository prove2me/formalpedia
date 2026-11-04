-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_with_maximal_edge_count__p2m_2f6efb11_cffe_4335_a64a_833cc169dca5_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:41:49.732592+00:00
-- url     : https://prove2.me/submissions/f08900e6-cbe4-42a5-882c-95c0fc026cc8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_edge_set__p2m_9bca3399_bc88_49f7_b83e_2aaaeb9cb6a3_a2
import Theorems.Thm_WilliamsonShmoys_planar_maximal_graph_edge_count__p2m_9bca3399_bc88_49f7_b83e_2aaaeb9cb6a3_a2
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (L : SimpleGraph V), HasPlanarDrawingOn L ∧
      ∃ (dL : DecidableRel L.Adj),
        (letI : DecidableRel L.Adj := dL;
          K.edgeFinset ⊆ L.edgeFinset ∧
          L.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨L, hL, dL, hprops⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_edge_set__p2m_9bca3399_bc88_49f7_b83e_2aaaeb9cb6a3_a2
      K hK
  letI : DecidableRel L.Adj := dL
  rcases hprops with ⟨hKL, hmax⟩
  refine ⟨L, hL, dL, ?_⟩
  refine ⟨hKL, ?_⟩
  exact WilliamsonShmoys.planar_maximal_graph_edge_count__p2m_9bca3399_bc88_49f7_b83e_2aaaeb9cb6a3_a2
    L hL hV hmax