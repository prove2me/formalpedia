-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:29:31.912648+00:00
-- url     : https://prove2.me/submissions/3efdef20-a579-4197-b40a-9f4bbf8cc926

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_fe58c870_e3e9_466f_b8e7_756f412ad0cc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_fe58c870_e3e9_466f_b8e7_756f412ad0cc

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_fe58c870_e3e9_466f_b8e7_756f412ad0cc G hG
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_fe58c870_e3e9_466f_b8e7_756f412ad0cc H hV hH hmax
  exact ⟨H, hGH, hH, hcount⟩