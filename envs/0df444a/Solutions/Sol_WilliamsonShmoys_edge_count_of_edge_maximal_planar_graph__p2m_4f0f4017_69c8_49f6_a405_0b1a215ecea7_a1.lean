-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_edge_maximal_planar_graph__p2m_4f0f4017_69c8_49f6_a405_0b1a215ecea7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:55:41.249597+00:00
-- url     : https://prove2.me/submissions/6e4b6651-913d-4c6a-97d0-4a84a389767a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_00360c86_73a0_483f_8c2b_2f99e65d88dd_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  obtain ⟨K, hHK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_00360c86_73a0_483f_8c2b_2f99e65d88dd_a1
      H hcard hH
  have hKH : K = H := hmax K hHK hKplanar
  subst K
  exact hKcount