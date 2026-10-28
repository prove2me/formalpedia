-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count_fixed_vertex_set
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:53:49.196042+00:00
-- url     : https://prove2.me/submissions/5c18a24b-3b2b-4332-a9ad-260249aa4b1e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ H : SimpleGraph V,
      M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hMH, hH, hcount⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_extension M hM hV
  have hHM : H ≤ M := hmax H hMH hH
  have hEq : H = M := le_antisymm hHM hMH
  simpa [hEq] using hcount