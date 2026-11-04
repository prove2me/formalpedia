-- Prove2me | solution 1 for WilliamsonShmoys.connected_maximal_drawable_graph_edge_count__p2m_7237be62_bb2d_4386_ba18_ecdd0c420d72_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:58:03.142836+00:00
-- url     : https://prove2.me/submissions/8f864ff4-a994-45ff-87f4-2160279bee9d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_dcda2b2e_bb79_4b65_906a_4b43dfb1e747_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_dcda2b2e_bb79_4b65_906a_4b43dfb1e747_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N)
    (hconn : N.Connected) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  have hup := WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_dcda2b2e_bb79_4b65_906a_4b43dfb1e747_a1 N hcard hN
  have hlo := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_dcda2b2e_bb79_4b65_906a_4b43dfb1e747_a1 N hcard hN hmax hconn
  exact Nat.le_antisymm hup hlo