-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:30:00.827035+00:00
-- url     : https://prove2.me/submissions/48b000c2-824e-4c9e-9bac-b275a5e086ee

import Theorems.Thm_WilliamsonShmoys_planar_connected_extension

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      (∀ u v, L.Adj u v → H.Adj u v) ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard :=
  WilliamsonShmoys.planar_connected_extension L hV hL
