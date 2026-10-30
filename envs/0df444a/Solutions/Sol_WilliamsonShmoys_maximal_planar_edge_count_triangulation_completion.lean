-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_triangulation_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:43:33.458205+00:00
-- url     : https://prove2.me/submissions/1923578b-5689-4b5e-b4b1-32d935e423df

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_repair
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_repair

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, R ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
  obtain ⟨T, hRT, hTdraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_repair
      (V := V) R hRdraw
  exact ⟨T, hRT, hTdraw,
    WilliamsonShmoys.maximal_planar_edge_count_repair
      (V := V) T hTdraw hCard hmax⟩