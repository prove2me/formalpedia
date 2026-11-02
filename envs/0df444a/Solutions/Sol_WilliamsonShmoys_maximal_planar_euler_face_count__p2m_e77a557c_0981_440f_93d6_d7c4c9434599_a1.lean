-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_face_count__p2m_e77a557c_0981_440f_93d6_d7c4c9434599_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:47:17.168723+00:00
-- url     : https://prove2.me/submissions/dfa7bdad-0a74-4071-8dd3-bf50d040aa1f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_c14927fd_3bb2_4aa2_8e62_690259e960a9_a1
import Theorems.Thm_WilliamsonShmoys_connected_graph_card_le_edge_ncard_add_one__p2m_c14927fd_3bb2_4aa2_8e62_690259e960a9_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by
  have hconn := WilliamsonShmoys.maximal_planar_drawing_connected__p2m_c14927fd_3bb2_4aa2_8e62_690259e960a9_a1 K hcard hK hmax
  have hedge := WilliamsonShmoys.connected_graph_card_le_edge_ncard_add_one__p2m_c14927fd_3bb2_4aa2_8e62_690259e960a9_a1 K hconn
  refine ⟨K.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega