-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_counts_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:37:50.130733+00:00
-- url     : https://prove2.me/submissions/f1188f72-337c-4a6e-a8fd-015fd63fc7dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_euler_counts_v2
import Theorems.Thm_WilliamsonShmoys_connected_card_le_edgeSet_add_one_v2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hConnected : L.Connected)
    (hCard : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = L.edgeSet.ncard + 2 /\
      3 * f <= 2 * L.edgeSet.ncard := by
  let e := L.edgeSet.ncard
  let v := Fintype.card V
  have he : e + 6 <= 3 * v :=
    WilliamsonShmoys.planar_drawing_edge_bound_for_euler_counts_v2
      L hLdraw hConnected hCard
  have hv : v <= e + 1 :=
    WilliamsonShmoys.connected_card_le_edgeSet_add_one_v2 L hConnected
  have hv' : v <= e + 2 := by omega
  refine ⟨e + 2 - v, ?_, ?_⟩ <;> dsimp [e, v] at * <;> omega