-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count_for_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:44:50.906774+00:00
-- url     : https://prove2.me/submissions/cd0afee3-da79-4837-8316-6aba848aad60

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulated_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hMax : ∀ W : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn W →
      (∀ u v, U.Adj u v → W.Adj u v) →
      ∀ u v, W.Adj u v → U.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = U.edgeSet.ncard + 6 := by
  obtain ⟨W, hW, hUW, hCount⟩ :=
    WilliamsonShmoys.planar_drawingOn_triangulated_supergraph
      U hU hCard
  have hWU : ∀ u v, W.Adj u v → U.Adj u v :=
    hMax W hW hUW
  have hEq : W = U := by
    ext u v
    exact ⟨hWU u v, hUW u v⟩
  simpa [hEq] using hCount