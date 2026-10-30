-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_edge_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:47:04.40684+00:00
-- url     : https://prove2.me/submissions/de3b4020-525e-4988-983f-fa1ed36425ab

import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨U, hTU, hU, hle, hcount⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_edge_count T hV hT
  omega