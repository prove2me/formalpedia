-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_triangulated_extension_f4cab8f1_36b2_49a4_9100_a8a3956b9d6e
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:25:06.981342+00:00
-- url     : https://prove2.me/submissions/e2d1150e-7178-4fc6-9ca2-220ea6205a96

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_edge_maximal_extension_e02108dc_5749_4b8c_85cc_e86e3f71cac7
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count_e02108dc_5749_4b8c_85cc_e86e3f71cac7
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLdraw, hLmax⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_has_edge_maximal_extension_e02108dc_5749_4b8c_85cc_e86e3f71cac7 K hKdraw
  have hCount := WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count_e02108dc_5749_4b8c_85cc_e86e3f71cac7
    L hLdraw hCard hLmax
  exact ⟨L, hKL, hLdraw, hCount⟩
