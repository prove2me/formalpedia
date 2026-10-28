-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:30:51.676143+00:00
-- url     : https://prove2.me/submissions/09885f91-a8ea-4e71-b4a7-bfc871e73a35
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hmono, hHcard⟩ :=
    WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc K hV hK
  omega