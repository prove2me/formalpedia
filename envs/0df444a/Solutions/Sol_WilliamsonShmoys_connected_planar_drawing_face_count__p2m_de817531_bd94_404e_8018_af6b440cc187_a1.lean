-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_face_count__p2m_de817531_bd94_404e_8018_af6b440cc187_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:45:24.05515+00:00
-- url     : https://prove2.me/submissions/829b139d-4dbf-4305-a20f-aac32a400dc1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_euler_characteristic_of_planar_drawing__p2m_7dadb7da_8b1f_4740_8afa_ded5b834878b_a2
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_7dadb7da_8b1f_4740_8afa_ded5b834878b_a2

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hCard : 3 <= Fintype.card V)
    (hConn : G.Connected) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun F : Nat => Exists fun B : Nat =>
      And (Fintype.card V + F = G.edgeSet.ncard + 2)
        (And (B = 2 * G.edgeSet.ncard) (3 * F <= B)) := by
  obtain ⟨F, hEuler⟩ :=
    WilliamsonShmoys.euler_characteristic_of_planar_drawing__p2m_7dadb7da_8b1f_4740_8afa_ded5b834878b_a2
      G hConn hG
  have hEdge :=
    WilliamsonShmoys.simple_planar_edge_bound__p2m_7dadb7da_8b1f_4740_8afa_ded5b834878b_a2
      G hCard hG
  refine ⟨F, 2 * G.edgeSet.ncard, hEuler, rfl, ?_⟩
  omega