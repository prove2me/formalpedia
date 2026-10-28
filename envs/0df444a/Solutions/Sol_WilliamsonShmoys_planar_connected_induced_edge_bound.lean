-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_induced_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:38:36.252996+00:00
-- url     : https://prove2.me/submissions/dd15f5fd-47bb-4610-8960-004ac91d8f74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_induced_edge_bound_small
import Theorems.Thm_WilliamsonShmoys_planar_connected_induced_edge_bound_large

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (S : Finset V)
    (hNonempty : S.Nonempty)
    (hConnected : (H.induce (↑S : Set V)).Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn
      (H.induce (↑S : Set V))) :
    (H.induce (↑S : Set V)).edgeSet.ncard ≤
      (if S.card < 3 then S.card / 2 else 3 * S.card - 6) := by
  by_cases hSmall : S.card < 3
  · simpa [hSmall] using
      WilliamsonShmoys.planar_connected_induced_edge_bound_small
        H S hNonempty hSmall
  · have hLarge : 3 ≤ S.card := Nat.le_of_not_lt hSmall
    simpa [hSmall] using
      WilliamsonShmoys.planar_connected_induced_edge_bound_large
        H S hConnected hDrawing hLarge