-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:23:48.722+00:00
-- url     : https://prove2.me/submissions/a632cfc1-444b-4744-a93b-c884a160866b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_local_step__p2m_db8af417_0538_4cad_8510_71b3310eaec4_a3
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_finite_saturation__p2m_db8af417_0538_4cad_8510_71b3310eaec4_a3

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ N.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (M.edgeSet.ncard : Int) ≤ (N.edgeSet.ncard : Int) := by
  obtain ⟨N, hMN, hNdraw, hNconn, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_finite_saturation__p2m_db8af417_0538_4cad_8510_71b3310eaec4_a3
      (P := fun G => WilliamsonShmoys.HasPlanarDrawingOn G)
      (hStep := by
        intro G hG hDisconnected
        obtain ⟨H, hGH, hHne, hHdraw⟩ :=
          WilliamsonShmoys.planar_drawing_connected_extension_local_step__p2m_db8af417_0538_4cad_8510_71b3310eaec4_a3
            G hG hDisconnected
        exact ⟨H, hGH, hHdraw, hHne⟩)
      M hM
  exact ⟨N, hMN, hNconn, hNdraw, hEdges⟩