-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_strict_supergraph_of_disconnected_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:22:31.94125+00:00
-- url     : https://prove2.me/submissions/e89079f2-2ecf-4ac8-8639-36395c0c38ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_finite_graph_has_unreachable_pair_34a43dbc_488e_44ec_bac5_5fafefe41c67
import Theorems.Thm_WilliamsonShmoys_add_edge_between_unreachable_vertices_preserving_planar_drawing_34a43dbc_488e_44ec_bac5_5fafefe41c67

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hDisconnected : ¬ K.Connected) :
    ∃ J : SimpleGraph V,
      K ≤ J ∧ ¬ J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn J := by
  obtain ⟨u, v, hUnreachable⟩ :=
    WilliamsonShmoys.disconnected_finite_graph_has_unreachable_pair_34a43dbc_488e_44ec_bac5_5fafefe41c67
      K hV hDisconnected
  exact WilliamsonShmoys.add_edge_between_unreachable_vertices_preserving_planar_drawing_34a43dbc_488e_44ec_bac5_5fafefe41c67
    K u v hUnreachable hDraw