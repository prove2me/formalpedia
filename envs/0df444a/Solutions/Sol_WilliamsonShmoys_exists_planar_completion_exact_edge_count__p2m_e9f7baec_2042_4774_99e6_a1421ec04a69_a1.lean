-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_completion_exact_edge_count__p2m_e9f7baec_2042_4774_99e6_a1421ec04a69_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:36:59.224805+00:00
-- url     : https://prove2.me/submissions/9b451ec4-3f77-4980-8479-0db53d7aef8f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_92669c9b_dd39_4b0e_bff1_b3f1c8b950b1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_92669c9b_dd39_4b0e_bff1_b3f1c8b950b1_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    Exists fun N : SimpleGraph V =>
      And (Set.Subset M.edgeSet N.edgeSet)
        (And (WilliamsonShmoys.HasPlanarDrawingOn N)
          (3 * Fintype.card V = N.edgeSet.ncard + 6)) := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_92669c9b_dd39_4b0e_bff1_b3f1c8b950b1_a1
      M hM
  refine Exists.intro N (And.intro hMN (And.intro hN ?_))
  exact WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_92669c9b_dd39_4b0e_bff1_b3f1c8b950b1_a1
    N hN hCard hmax