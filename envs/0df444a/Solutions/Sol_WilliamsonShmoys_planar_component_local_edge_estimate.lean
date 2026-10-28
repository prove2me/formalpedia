-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_local_edge_estimate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:30:48.85098+00:00
-- url     : https://prove2.me/submissions/c1262634-a0ba-4c99-a994-f39c470af991
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_connected_induced_edge_bound
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (C : Finset (Finset V))
    (hPartition : (∀ S ∈ C, S.Nonempty) ∧
      ∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S)
    (hConnected : ∀ S ∈ C, (H.induce (↑S : Set V)).Connected)
    (hDrawing : ∀ S ∈ C, WilliamsonShmoys.HasPlanarDrawingOn
      (H.induce (↑S : Set V))) :
    ∀ S ∈ C,
      (H.induce (↑S : Set V)).edgeSet.ncard ≤
        (if S.card < 3 then S.card / 2 else 3 * S.card - 6) := by
  intro S hS
  exact WilliamsonShmoys.planar_connected_induced_edge_bound H S
    (hPartition.1 S hS) (hConnected S hS) (hDrawing S hS)