-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_strict_supergraph_of_unreachable_pair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T03:08:25.513637+00:00
-- url     : https://prove2.me/submissions/6a3b2619-d303-47da-893d-2e6c74c05998
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_edge_between_unreachable_vertices
import Theorems.Thm_WilliamsonShmoys_adj_reachable

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V)
    (hUnreach : Not (G.Reachable u v)) :
    Exists fun H : SimpleGraph V =>
      And (G <= H)
        (And (WilliamsonShmoys.HasPlanarDrawingOn H) (Not (H <= G))) := by
  obtain ⟨H, hGH, hHdraw, huv⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_edge_between_unreachable_vertices
      G hdraw u v hUnreach
  refine ⟨H, hGH, hHdraw, ?_⟩
  intro hHG
  exact hUnreach (WilliamsonShmoys.adj_reachable G (hHG huv))