-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_formula
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:10:13.033518+00:00
-- url     : https://prove2.me/submissions/4bc1aaf7-93af-4935-ad59-b747e5bc6087
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_connected
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_equation

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 := by
  have hConnected : L.Connected :=
    WilliamsonShmoys.maximal_planar_connected L hL hMax hCard
  exact WilliamsonShmoys.connected_planar_euler_equation L hL hConnected hCard