-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_euler_20261028
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:17:59.630721+00:00
-- url     : https://prove2.me/submissions/b38a7aaa-e8a3-4e1f-8656-2c50cc7242b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_connected_extension_of_local_step
import Theorems.Thm_WilliamsonShmoys_planar_drawing_local_edge_extension_nonempty

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V,
      H ≤ G ∧ G.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn G := by
  obtain ⟨G, hHG, hDrawG, hConn⟩ :=
    WilliamsonShmoys.exists_connected_extension_of_local_step
      (P := fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K)
      (fun K hK hNotConn =>
        WilliamsonShmoys.planar_drawing_local_edge_extension_nonempty
          K hV hK hNotConn)
      H hDraw
  exact ⟨G, hHG, hConn, hDrawG⟩