-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_face_count_bound__p2m_af58f30d_9690_4bf2_bfba_5c068b1bd46b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:45:54.7125+00:00
-- url     : https://prove2.me/submissions/5c35d37f-6e58-42be-aa73-80eb2b54b2dd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_simple_edge_bound__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn G) (hConnected : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    Exists fun f : Nat => And
      (Fintype.card V + f = G.edgeSet.ncard + 2)
      (3 * f <= 2 * G.edgeSet.ncard) := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1
      G hDraw hConnected
  have hEdge :=
    WilliamsonShmoys.connected_planar_simple_edge_bound__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1
      G hDraw hConnected hCard
  refine ⟨f, hEuler, ?_⟩
  omega