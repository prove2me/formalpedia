-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_of_disconnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:17:35.673346+00:00
-- url     : https://prove2.me/submissions/3e19006d-b759-4ab5-aab2-e971220282a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_disconnected_has_unreachable_pair_e285668e
import Theorems.Thm_WilliamsonShmoys_planar_augment_unreachable_pair_e285668e

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hDisconnected : ¬ L.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ M ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn M := by
  obtain ⟨u, v, huv, hUnreachable⟩ :=
    WilliamsonShmoys.disconnected_has_unreachable_pair_e285668e L hDisconnected hCard
  exact WilliamsonShmoys.planar_augment_unreachable_pair_e285668e
    L hL u v huv hUnreachable