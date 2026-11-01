-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_triangulation_extension__p2m_126577ef_f856_473b_b1f2_d55f4854fb26_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:55:32.951143+00:00
-- url     : https://prove2.me/submissions/5d94b120-71b9-449c-9ead-5deb6f3313d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension__p2m_b4f778a6_f898_4626_8a06_345c4a75a344_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_graph_edge_count__p2m_b4f778a6_f898_4626_8a06_345c4a75a344_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        (letI : DecidableRel L.Adj := Classical.decRel L.Adj
         L.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_extension__p2m_b4f778a6_f898_4626_8a06_345c4a75a344_a2
      K hcard hK
  refine ⟨L, hKL, hL, ?_⟩
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  exact WilliamsonShmoys.maximal_drawable_planar_graph_edge_count__p2m_b4f778a6_f898_4626_8a06_345c4a75a344_a2
    L hcard hL hmax