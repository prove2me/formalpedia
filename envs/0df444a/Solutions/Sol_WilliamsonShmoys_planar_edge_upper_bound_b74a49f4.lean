-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_b74a49f4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:58:09.350437+00:00
-- url     : https://prove2.me/submissions/e00e0b4d-1298-49e5-a4c3-2c49598b25d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_upper_bound_b74a49f4
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_b74a49f4

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hSub, hCardle, hConnected, hDrawing⟩ :=
    WilliamsonShmoys.planar_connected_supergraph_b74a49f4 K hK hCard
  have hBound :=
    WilliamsonShmoys.planar_connected_edge_upper_bound_b74a49f4
      H hDrawing hConnected hCard
  exact (Nat.add_le_add_right hCardle 6).trans hBound