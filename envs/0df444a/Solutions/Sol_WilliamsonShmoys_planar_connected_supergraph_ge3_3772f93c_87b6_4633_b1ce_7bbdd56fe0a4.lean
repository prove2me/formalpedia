-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph_ge3_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:49:14.335556+00:00
-- url     : https://prove2.me/submissions/3da4a33f-4690-45b1-89a3-b62bfa3b7561
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_strict_extension
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_components

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected := by
  apply WilliamsonShmoys.exists_connected_supergraph_of_strict_extension
      (P := WilliamsonShmoys.HasPlanarDrawingOn) K hKdraw
  intro G hKG hGdraw hGdisconnected
  obtain ⟨u, v, huv, H, hlt, hHdraw, _hBridge⟩ :=
    WilliamsonShmoys.planar_drawing_add_edge_between_components
      G hGdraw hCard hGdisconnected
  exact ⟨H, hlt, hHdraw⟩