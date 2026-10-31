-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_d3131f9d_f6af_4764_8ee2_8200821979d2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:43:47.249372+00:00
-- url     : https://prove2.me/submissions/cb462f69-2057-4016-ac44-c24b18740743

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_886ba71e_17fb_4cdf_ac77_08f2d3101909_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ G : SimpleGraph V,
      H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G = H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨G, hHG, hG, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_886ba71e_17fb_4cdf_ac77_08f2d3101909_a1
      H hH hV
  have hGH : G = H := hmax G hHG hG
  rw [hGH] at hcount
  exact hcount