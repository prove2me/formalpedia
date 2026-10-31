-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawable_edge_bound__p2m_2c5adea4_d505_4326_974e_37a0f04a34d9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:58.999783+00:00
-- url     : https://prove2.me/submissions/44095ac2-093f-4f99-a021-6e3cfed0621e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_certificate__p2m_e1f0e5cb_88a1_4c02_a6cc_5b5efd64f417_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  have hcert :=
    WilliamsonShmoys.connected_planar_euler_certificate__p2m_e1f0e5cb_88a1_4c02_a6cc_5b5efd64f417_a1
      H hConn hDraw hCard
  let F := Classical.choose hcert
  have hbounds := Classical.choose_spec hcert
  omega
