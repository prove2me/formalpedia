-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_upper_bound_d974173a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:07:01.121832+00:00
-- url     : https://prove2.me/submissions/6bc0fc61-c7ae-4e9e-baff-4eec8d172d61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connectivity_extension_e2002294_532e_4f58_bb0b_2f40f61d66b4
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_e2002294_532e_4f58_bb0b_2f40f61d66b4

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K', hsub, hconn, hdraw', hcard⟩ :=
    WilliamsonShmoys.planar_drawing_connectivity_extension_e2002294_532e_4f58_bb0b_2f40f61d66b4
      K hdraw hV
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_bound_e2002294_532e_4f58_bb0b_2f40f61d66b4
      K' hconn hdraw' hV
  omega
