-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:01:10.063074+00:00
-- url     : https://prove2.me/submissions/70a43626-3bb7-442c-a314-8bf2c436367d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hmax : ∀ G : SimpleGraph V,
      H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G ≤ H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨G, hHG, hG, hcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_completion H hV hH hconn
  have hGH : G ≤ H := hmax G hHG hG
  have hEq : H = G := le_antisymm hHG hGH
  rw [hEq]
  exact hcount