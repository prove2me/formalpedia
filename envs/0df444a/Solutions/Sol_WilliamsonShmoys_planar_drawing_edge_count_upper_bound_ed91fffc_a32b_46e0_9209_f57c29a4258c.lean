-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound_ed91fffc_a32b_46e0_9209_f57c29a4258c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:32:49.200357+00:00
-- url     : https://prove2.me/submissions/23c0ef58-47f3-4b38-9a1a-9cb094ae4729

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_05250361_edf9_4bba_b0bb_f1c9e6abc2aa

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    (M.edgeSet.ncard : Int) <=
      (3 : Int) * (Fintype.card V : Int) - 6 := by
  obtain ⟨Q, hMQ, _hQ, hcard_le, hcard_eq⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_05250361_edf9_4bba_b0bb_f1c9e6abc2aa M hV hM
  omega