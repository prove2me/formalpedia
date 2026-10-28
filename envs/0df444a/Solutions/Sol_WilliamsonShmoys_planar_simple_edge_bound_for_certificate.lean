-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound_for_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:12:30.290533+00:00
-- url     : https://prove2.me/submissions/f88803a9-7153-445f-94dd-aacbd3ac83a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_for_certificate_38ffb807
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_for_certificate_38ffb807
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_extension_data_for_certificate_38ffb807

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  apply WilliamsonShmoys.planar_edge_bound_from_extension_data_for_certificate_38ffb807
    K hV hdraw
  · exact WilliamsonShmoys.planar_drawing_connected_extension_for_certificate_38ffb807
      K hV hdraw
  · intro G hG hconn hGdraw
    exact WilliamsonShmoys.connected_planar_edge_bound_for_certificate_38ffb807
      G hG hconn hGdraw