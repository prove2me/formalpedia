-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangular_incidence__p2m_addb50df_8cce_4ac7_84ef_2e1f35b931aa_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:49:00.310164+00:00
-- url     : https://prove2.me/submissions/646b88ff-4ed8-4e9e-8c05-2aa40a4758f1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_790c0277_1cda_4997_aaa7_2744ce166f52_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → H ≤ L → L = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     ∀ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 →
        3 * f = 2 * H.edgeFinset.card) := by
  intro f hEuler
  have hEdge :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_790c0277_1cda_4997_aaa7_2744ce166f52_a1
      H hcard hdraw hmax
  omega