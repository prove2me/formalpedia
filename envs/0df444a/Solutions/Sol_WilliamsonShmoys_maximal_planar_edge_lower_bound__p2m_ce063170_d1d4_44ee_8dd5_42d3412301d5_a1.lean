-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ce063170_d1d4_44ee_8dd5_42d3412301d5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:59:41.676849+00:00
-- url     : https://prove2.me/submissions/abdef62e-4556-49f9-b7a3-c3f1f8e2419d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_triangulation__p2m_28e242ed_6a11_4ce9_a3c7_bb69d8d26f7b_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    3 * Fintype.card V <= L.edgeFinset.card + 6 := by
  obtain ⟨f, hEuler, hTriangulation⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_euler_triangulation__p2m_28e242ed_6a11_4ce9_a3c7_bb69d8d26f7b_a2
      L hL hmax hcard
  omega