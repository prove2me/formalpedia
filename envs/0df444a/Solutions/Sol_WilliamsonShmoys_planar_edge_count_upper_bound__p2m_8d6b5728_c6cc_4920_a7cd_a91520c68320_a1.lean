-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_8d6b5728_c6cc_4920_a7cd_a91520c68320_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:34:50.051206+00:00
-- url     : https://prove2.me/submissions/8d84878f-0f7e-4ebb-addf-0064d4923df3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_connected_induced_bounds__p2m_ac18a95b_13f8_4a76_980e_021bef74dbe9_a1
import Theorems.Thm_WilliamsonShmoys_connected_induced_planar_edge_bound__p2m_ac18a95b_13f8_4a76_980e_021bef74dbe9_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  exact WilliamsonShmoys.planar_edge_bound_from_connected_induced_bounds__p2m_ac18a95b_13f8_4a76_980e_021bef74dbe9_a1
    N dN hcard
    (WilliamsonShmoys.connected_induced_planar_edge_bound__p2m_ac18a95b_13f8_4a76_980e_021bef74dbe9_a1
      N dN hN)