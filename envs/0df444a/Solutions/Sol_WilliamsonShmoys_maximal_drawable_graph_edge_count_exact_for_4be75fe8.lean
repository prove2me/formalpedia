-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_exact_for_4be75fe8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:56:37.082384+00:00
-- url     : https://prove2.me/submissions/fd3caecc-6166-44c6-b4e0-0c56a0da29ac

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ H : SimpleGraph V, M ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hMH, hH, hcount⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_edge_count M hV hM
  have hEq : H = M := hMax H hMH hH
  simpa [hEq] using hcount