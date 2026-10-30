-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_f8388283_f9ed_4c0f_b0f7_c6403411f5ff_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:30:20.97722+00:00
-- url     : https://prove2.me/submissions/09dcac1d-cb48-4ddf-97ad-0c6de7f53cf1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_49092f42_4606_480d_84ab_7522b76f4e32_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_of_connected_bound__p2m_49092f42_4606_480d_84ab_7522b76f4e32_a2
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 <= Fintype.card V) : X.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_drawing_edge_bound_of_connected_bound__p2m_49092f42_4606_480d_84ab_7522b76f4e32_a2
    (fun W _ _ Y hc hd hn =>
      WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_49092f42_4606_480d_84ab_7522b76f4e32_a2
        Y hd hc hn) X hX hV