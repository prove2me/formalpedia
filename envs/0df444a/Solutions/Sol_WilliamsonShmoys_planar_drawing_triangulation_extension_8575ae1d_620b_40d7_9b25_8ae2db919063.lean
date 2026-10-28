-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_8575ae1d_620b_40d7_9b25_8ae2db919063
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:55:25.243313+00:00
-- url     : https://prove2.me/submissions/d894cb05-6c69-4cc1-9db9-41c4222a7096
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_to_maximal_f2db904c_5721_454a_bbac_7987a5a61819
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_f2db904c_5721_454a_bbac_7987a5a61819

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hQconn : Q.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      R.Connected ∧
      R.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨R, hQR, hRdraw, hRconn, hRmax⟩ :=
    WilliamsonShmoys.planar_drawing_extension_to_maximal_f2db904c_5721_454a_bbac_7987a5a61819
      Q hQdraw hQconn hCard
  refine ⟨R, hQR, hRdraw, hRconn, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count_f2db904c_5721_454a_bbac_7987a5a61819
    R hRdraw hRmax hCard