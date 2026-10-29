-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_local_edge_extension_nonempty
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T01:54:09.706894+00:00
-- url     : https://prove2.me/submissions/8b8b39e4-3221-4c2c-bb1d-7e34b124a3c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augment_to_edge_bound
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximum_edge_count_connected

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hNotConn : ¬ H.Connected) :
    ∃ L : SimpleGraph V, H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∃ u v : V, L.Adj u v ∧ ¬ H.Adj u v := by
  obtain ⟨K, hHK, hKDraw, hKEdges⟩ :=
    WilliamsonShmoys.planar_drawing_augment_to_edge_bound H hDraw hV
  have hKConn :=
    WilliamsonShmoys.planar_drawing_maximum_edge_count_connected K hKDraw hV hKEdges
  have hNew : ∃ u v : V, K.Adj u v ∧ ¬ H.Adj u v := by
    by_contra hnone
    have hKH : K ≤ H := by
      intro u v huv
      by_contra hnot
      exact hnone ⟨u, v, huv, hnot⟩
    have hEq : K = H := le_antisymm hKH hHK
    exact hNotConn (hEq ▸ hKConn)
  obtain ⟨u, v, hKuv, hHnot⟩ := hNew
  exact ⟨K, hHK, hKDraw, u, v, hKuv, hHnot⟩