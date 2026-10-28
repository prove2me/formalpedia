-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_job_09cd0f78_596e_4a94_9326_038b3be8d638
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:03:36.64219+00:00
-- url     : https://prove2.me/submissions/d55acea2-623c-4fb4-bee0-a800d864281d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_0359c2de_483c_4e08_9117_cd9dcde287a8

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hsub, hH, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_completion_0359c2de_483c_4e08_9117_cd9dcde287a8 L hL hV
  have hle : L.edgeSet.ncard <= H.edgeSet.ncard := Set.ncard_mono hsub
  omega