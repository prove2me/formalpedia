-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_disconnected_edge_extension_ge_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:13:05.261265+00:00
-- url     : https://prove2.me/submissions/a403c908-0e7f-4c92-b24e-4768145f662e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_has_nonadjacent_pair
import Theorems.Thm_WilliamsonShmoys_planar_drawing_cross_component_edge_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ¬ K ≤ H := by
  obtain ⟨u, v, huv_ne, huv_not_reachable, huv_not_adj⟩ :=
    WilliamsonShmoys.planar_drawing_disconnected_has_nonadjacent_pair
      H hV hDisconnected
  obtain ⟨K, hHK, hK, huvK⟩ :=
    WilliamsonShmoys.planar_drawing_cross_component_edge_extension
      H hH u v huv_not_reachable
  refine ⟨K, hHK, hK, ?_⟩
  intro hKH
  exact huv_not_adj (hKH huvK)