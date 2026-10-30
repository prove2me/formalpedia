-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_data__p2m_e3b94d84_a772_4bbe_8d1c_d23630bc7e79_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:18:53.143049+00:00
-- url     : https://prove2.me/submissions/5ad9bbb5-38b8-41ae-8bb3-8ced1882d463
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_6958ede2_46bd_4413_bb7d_9bd4b5c0d4f2_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_6958ede2_46bd_4413_bb7d_9bd4b5c0d4f2_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hHconn : H.Connected) (hHplanar : HasPlanarDrawingOn H) :
    Exists fun f : Nat => And (Fintype.card V + f = H.edgeSet.ncard + 2)
      (3 * f <= 2 * H.edgeSet.ncard) := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count__p2m_6958ede2_46bd_4413_bb7d_9bd4b5c0d4f2_a2
      H hV hHconn hHplanar
  refine ⟨f, hEuler, ?_⟩
  have hEdge :=
    WilliamsonShmoys.planar_drawing_edge_bound__p2m_6958ede2_46bd_4413_bb7d_9bd4b5c0d4f2_a2
      H hV hHplanar
  omega
