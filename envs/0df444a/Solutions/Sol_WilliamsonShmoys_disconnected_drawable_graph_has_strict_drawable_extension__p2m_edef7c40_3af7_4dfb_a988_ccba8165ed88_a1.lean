-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_drawable_graph_has_strict_drawable_extension__p2m_edef7c40_3af7_4dfb_a988_ccba8165ed88_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:13:46.511909+00:00
-- url     : https://prove2.me/submissions/2948bacd-0772-4260-b2e3-f795404f6a2d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_ordered_unreachable_cut__p2m_41ac2ad2_1442_40d5_933f_adb24d67ad24_a3
import Theorems.Thm_WilliamsonShmoys_planar_drawing_glue_across_edge_free_cut__p2m_41ac2ad2_1442_40d5_933f_adb24d67ad24_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ L.Connected) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧ L ≤ M ∧ L ≠ M := by
  obtain ⟨u, v, S, huv, hUnreachable, hNotAdj, hu, hv, hCut⟩ :=
    WilliamsonShmoys.disconnected_ordered_unreachable_cut__p2m_41ac2ad2_1442_40d5_933f_adb24d67ad24_a3
      L hCard hNotConnected
  obtain ⟨M, hM, hLM, hMuv⟩ :=
    WilliamsonShmoys.planar_drawing_glue_across_edge_free_cut__p2m_41ac2ad2_1442_40d5_933f_adb24d67ad24_a3
      L hL S u v hu hv hCut
  refine ⟨M, hM, hLM, ?_⟩
  intro hEq
  subst M
  exact hNotAdj hMuv