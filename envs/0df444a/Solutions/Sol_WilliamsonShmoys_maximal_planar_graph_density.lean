-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_density
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:25:50.24403+00:00
-- url     : https://prove2.me/submissions/880d1d1b-533c-4f14-b436-97cc934ff922

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_maximal_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, HasPlanarDrawingOn M →
      (∀ u v, L.Adj u v → M.Adj u v) → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨T, hT, hLT, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_with_maximal_edge_count L hL hCard
  have hTL : T = L := hmax T hT hLT
  rw [hTL] at hcount
  omega