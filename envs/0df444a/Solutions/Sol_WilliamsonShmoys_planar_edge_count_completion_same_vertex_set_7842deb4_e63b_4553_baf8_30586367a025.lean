-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_completion_same_vertex_set_7842deb4_e63b_4553_baf8_30586367a025
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:22:34.304234+00:00
-- url     : https://prove2.me/submissions/eec22b08-0389-47c6-a7ee-5861bbee4890
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_same_vertex_set_7842deb4_e63b_4553_baf8_30586367a025
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_7842deb4_e63b_4553_baf8_30586367a025

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V,
      R ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧
        3 * Fintype.card V = S.edgeSet.ncard + 6 := by
  obtain ⟨S, hRS, hSdraw, hSmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_same_vertex_set_7842deb4_e63b_4553_baf8_30586367a025
      R hRdraw
  have hCount :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count_7842deb4_e63b_4553_baf8_30586367a025
      S hSdraw hCard hSmax
  exact ⟨S, hRS, hSdraw, hCount⟩