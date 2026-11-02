-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:08:50.730852+00:00
-- url     : https://prove2.me/submissions/b722e5ad-e508-4b97-9ca8-51e28fe9e3f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_reachable_pair__p2m_02da0ff6_1020_4ffd_8f79_c5b3eb2fc9a4_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_iterated_bridge_connected__p2m_02da0ff6_1020_4ffd_8f79_c5b3eb2fc9a4_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ G.Connected ∧ HasPlanarDrawingOn G := by
  classical
  obtain ⟨G, hHG, hG, hconn⟩ :=
    WilliamsonShmoys.planar_drawing_iterated_bridge_connected__p2m_02da0ff6_1020_4ffd_8f79_c5b3eb2fc9a4_a2
      (H := H) hH
      (by
        intro K hHK hK a b hab
        exact WilliamsonShmoys.planar_drawing_add_reachable_pair__p2m_02da0ff6_1020_4ffd_8f79_c5b3eb2fc9a4_a2
          (H := K) hK hab)
  exact ⟨G, hHG, hconn, hG⟩