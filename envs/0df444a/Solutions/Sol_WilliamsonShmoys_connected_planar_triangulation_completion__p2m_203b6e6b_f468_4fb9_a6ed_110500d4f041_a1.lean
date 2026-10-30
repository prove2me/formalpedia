-- Prove2me | solution 1 for WilliamsonShmoys_connected_planar_triangulation_completion__p2m_203b6e6b_f468_4fb9_a6ed_110500d4f041_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:54:16.233642+00:00
-- url     : https://prove2.me/submissions/e6a133a6-ee57-4034-a57a-0fbbf963f6bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_d5fb2175_2340_4982_8e4d_d8f2c0e58052_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_d5fb2175_2340_4982_8e4d_d8f2c0e58052_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G)
    (hConnected : G.Connected) (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHDraw, hMax⟩ :=
    WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_d5fb2175_2340_4982_8e4d_d8f2c0e58052_a1
      G hDraw hConnected hCard
  have hCount :=
    WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_d5fb2175_2340_4982_8e4d_d8f2c0e58052_a1
      H hHDraw hMax hCard
  exact ⟨H, hGH, hHDraw, hCount⟩