-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:43:29.737056+00:00
-- url     : https://prove2.me/submissions/bbbeff01-e47c-4b7c-addd-251ce8fffd12
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound_completion_aad8d6c4
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, hle, hcard, hplanar⟩ :=
    WilliamsonShmoys.planar_connected_edge_bound_completion_aad8d6c4 K hV hconn hK
  simpa [hcard] using hle