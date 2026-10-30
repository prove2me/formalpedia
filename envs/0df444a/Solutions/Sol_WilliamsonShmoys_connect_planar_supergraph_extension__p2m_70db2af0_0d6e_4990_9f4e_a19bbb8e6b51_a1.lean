-- Prove2me | solution 1 for WilliamsonShmoys.connect_planar_supergraph_extension__p2m_70db2af0_0d6e_4990_9f4e_a19bbb8e6b51_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:45:44.543971+00:00
-- url     : https://prove2.me/submissions/88f1ba61-7548-42c3-a743-90aafe82a539
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_extension__p2m_0bb86acf_18ae_4f3f_97ae_6c52ab0a1177_a4
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_connected__p2m_0bb86acf_18ae_4f3f_97ae_6c52ab0a1177_a4
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, L.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hLH, hHDraw, hMax⟩ :=
    WilliamsonShmoys.planar_edge_maximal_extension__p2m_0bb86acf_18ae_4f3f_97ae_6c52ab0a1177_a4
      L hDraw hV
  exact ⟨H, hLH,
    WilliamsonShmoys.edge_maximal_planar_connected__p2m_0bb86acf_18ae_4f3f_97ae_6c52ab0a1177_a4
      H hV hHDraw hMax,
    hHDraw⟩