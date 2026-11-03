-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4c675a48_b2e7_41d9_8987_0c6f38bd3a34_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:46:50.464029+00:00
-- url     : https://prove2.me/submissions/9ad456ae-995f-4875-8892-321522cf8e0f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_43a07344_7f08_4c1d_acca_1e4a761282d7_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_43a07344_7f08_4c1d_acca_1e4a761282d7_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :=
    WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_43a07344_7f08_4c1d_acca_1e4a761282d7_a1
      M hcard hM
  have hlower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_43a07344_7f08_4c1d_acca_1e4a761282d7_a1
      M hcard hM hmax
  omega