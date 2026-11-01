-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_a2ea7bef_e32d_429b_9bbe_071fb272fdb7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:50:53.521845+00:00
-- url     : https://prove2.me/submissions/cd037db2-ca0f-402a-a24b-877ba5944055
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_extension__p2m_977ef0e9_2b10_4ce9_abb8_e8741d8c6875_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_of_bridges__p2m_977ef0e9_2b10_4ce9_abb8_e8741d8c6875_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.planar_drawing_connected_supergraph_of_bridges__p2m_977ef0e9_2b10_4ce9_abb8_e8741d8c6875_a1
    K dK hK
    (fun G dG hG u v hsep =>
      WilliamsonShmoys.planar_drawing_bridge_extension__p2m_977ef0e9_2b10_4ce9_abb8_e8741d8c6875_a1
        G dG hG u v hsep)