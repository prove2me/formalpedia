-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:32:07.364995+00:00
-- url     : https://prove2.me/submissions/43049297-f996-4a96-8bd2-2e3e3fd635ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_of_disconnected

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    L.Connected := by
  by_contra hNotConnected
  obtain ⟨M, hLM, hMNe, hM⟩ :=
    WilliamsonShmoys.planar_supergraph_of_disconnected L hL hNotConnected hCard
  exact hMNe (hMax M hLM hM)