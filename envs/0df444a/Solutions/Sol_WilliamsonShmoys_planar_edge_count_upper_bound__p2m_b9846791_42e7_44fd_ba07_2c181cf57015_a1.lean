-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_b9846791_42e7_44fd_ba07_2c181cf57015_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:06:56.404951+00:00
-- url     : https://prove2.me/submissions/41d9cac5-9e36-4854-b7fe-00c4efed4d73

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph__p2m_0d510956_7da0_4290_84d6_372bf969c07f_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_0d510956_7da0_4290_84d6_372bf969c07f_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  obtain ⟨N, hMN, hconn, hNplanar, hcard⟩ :=
    WilliamsonShmoys.connected_planar_supergraph__p2m_0d510956_7da0_4290_84d6_372bf969c07f_a1
      M hV hM
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_0d510956_7da0_4290_84d6_372bf969c07f_a1
      N hV hNplanar hconn
  omega