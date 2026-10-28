-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_upper_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:22:23.317269+00:00
-- url     : https://prove2.me/submissions/75c89fd6-d07a-41c4-970d-6374467116e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_augmentation_for_euler_bound
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_of_subgraph_of_extremal_planar
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHHdraw, hHE⟩ :=
    WilliamsonShmoys.planar_drawing_edge_bound_augmentation_for_euler_bound G hV hG
  exact WilliamsonShmoys.planar_drawing_edge_bound_of_subgraph_of_extremal_planar
    G H hV hGH hHE
