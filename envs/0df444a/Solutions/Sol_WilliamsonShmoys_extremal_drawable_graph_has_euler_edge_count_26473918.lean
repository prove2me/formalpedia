-- Prove2me | solution 1 for WilliamsonShmoys.extremal_drawable_graph_has_euler_edge_count_26473918
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:05:58.288422+00:00
-- url     : https://prove2.me/submissions/3f54c2ee-2d44-4a4a-a43d-6b72055e1e03

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_edge_count_26473918
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hNmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hKdraw, hKcount⟩ :=
    WilliamsonShmoys.planar_supergraph_with_euler_edge_count_26473918 N hNdraw hCard
  have hKN : K ≤ N := hNmax K hNK hKdraw
  have hEq : K = N := le_antisymm hKN hNK
  simpa [hEq] using hKcount