-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_certificate__p2m_e1f0e5cb_88a1_4c02_a6cc_5b5efd64f417_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:17:40.185444+00:00
-- url     : https://prove2.me/submissions/e5713268-d96f-4e0f-ac35-961e3ec73c16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_characteristic__p2m_2c120eb1_ceed_4c13_9974_ca3513a96318_a1
import Theorems.Thm_WilliamsonShmoys_connected_simple_planar_edge_bound__p2m_2c120eb1_ceed_4c13_9974_ca3513a96318_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hDraw : HasPlanarDrawingOn H) (hCard : 3 <= Fintype.card V) :
    ∃ F : ℕ, (3 * F <= 2 * H.edgeSet.ncard) ∧
      (Fintype.card V + F = H.edgeSet.ncard + 2) := by
  obtain ⟨F, hEuler⟩ :=
    WilliamsonShmoys.connected_planar_euler_characteristic__p2m_2c120eb1_ceed_4c13_9974_ca3513a96318_a1
      H hConn hDraw
  have hEdge :=
    WilliamsonShmoys.connected_simple_planar_edge_bound__p2m_2c120eb1_ceed_4c13_9974_ca3513a96318_a1
      H hConn hDraw hCard
  refine ⟨F, ?_, hEuler⟩
  omega