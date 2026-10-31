-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_connected_supergraph__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:39:46.800352+00:00
-- url     : https://prove2.me/submissions/51ecb6cd-b6ff-4e2e-a026-f5cf4f9ba8ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_one_bridge__p2m_7397eada_aa5d_4bc5_889b_e16ea7056544_a1
import Theorems.Thm_WilliamsonShmoys_iterate_planar_bridges__p2m_7397eada_aa5d_4bc5_889b_e16ea7056544_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ G.Connected ∧ HasPlanarDrawingOn G ∧
      H.edgeSet.ncard ≤ G.edgeSet.ncard := by
  obtain ⟨G, hHG, hGconn, hGplanar⟩ :=
    WilliamsonShmoys.iterate_planar_bridges__p2m_7397eada_aa5d_4bc5_889b_e16ea7056544_a1
      H hH
      (fun K hHK hK hKdisc =>
        WilliamsonShmoys.planar_drawing_one_bridge__p2m_7397eada_aa5d_4bc5_889b_e16ea7056544_a1
          K hK hKdisc)
  exact ⟨G, hHG, hGconn, hGplanar,
    Set.ncard_mono (SimpleGraph.edgeSet_mono hHG)⟩