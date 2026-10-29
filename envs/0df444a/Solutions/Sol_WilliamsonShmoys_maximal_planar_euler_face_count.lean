-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_face_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:53:09.695012+00:00
-- url     : https://prove2.me/submissions/b45e2274-9049-4e9a-8d7c-62c1c8bcbd65
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_connected__p2m_367e7ff6_f47c_4801_a657_f77b95acb1d0_a3
import Theorems.Thm_WilliamsonShmoys_connected_graph_edge_count_lower_bound__p2m_367e7ff6_f47c_4801_a657_f77b95acb1d0_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 := by
  have hConn : H.Connected :=
    WilliamsonShmoys.maximal_drawable_graph_connected__p2m_367e7ff6_f47c_4801_a657_f77b95acb1d0_a3
      H hDraw hMax hCard
  have hEdgeLower : Fintype.card V ≤ H.edgeSet.ncard + 1 :=
    WilliamsonShmoys.connected_graph_edge_count_lower_bound__p2m_367e7ff6_f47c_4801_a657_f77b95acb1d0_a3
      H hConn
  refine ⟨H.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega
