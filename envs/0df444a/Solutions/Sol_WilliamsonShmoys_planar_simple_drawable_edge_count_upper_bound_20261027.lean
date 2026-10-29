-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_drawable_edge_count_upper_bound_20261027
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:40:21.752781+00:00
-- url     : https://prove2.me/submissions/2f9ca115-02dd-45e0-8624-5503cfefd100

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_20261027
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_20261027

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hsub, hcard, hHplanar, hHmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension_20261027 G hV hGplanar
  have hHcount := WilliamsonShmoys.maximal_planar_edge_count_20261027 H hV hHplanar hHmax
  omega