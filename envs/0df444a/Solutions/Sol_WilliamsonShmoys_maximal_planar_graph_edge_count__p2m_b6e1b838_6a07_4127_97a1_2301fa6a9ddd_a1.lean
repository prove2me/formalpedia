-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b6e1b838_6a07_4127_97a1_2301fa6a9ddd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:52:32.978763+00:00
-- url     : https://prove2.me/submissions/1abe047d-3cf9-4bca-903d-5764dcbc0d16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_0a96650e_3562_4e4d_ac7d_bc404fba85ef_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_lower_bound__p2m_0a96650e_3562_4e4d_ac7d_bc404fba85ef_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  exact Nat.le_antisymm
    (WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_0a96650e_3562_4e4d_ac7d_bc404fba85ef_a1
      N hcard hN)
    (WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_0a96650e_3562_4e4d_ac7d_bc404fba85ef_a1
      N hcard hN hmax)