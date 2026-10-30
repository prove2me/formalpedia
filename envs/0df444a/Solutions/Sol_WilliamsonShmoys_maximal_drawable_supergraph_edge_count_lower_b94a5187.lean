-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_edge_count_lower_b94a5187
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:59:03.343816+00:00
-- url     : https://prove2.me/submissions/8d428994-1354-49a4-a457-0b3b237e2263

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_triangulation_edge_lower

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by
  obtain ⟨L, hKL, hLdraw, hLcount⟩ :=
    WilliamsonShmoys.drawable_graph_triangulation_edge_lower K hV hKdraw
  have hLK : L <= K := hmax L hKL hLdraw
  have hEq : L = K := le_antisymm hLK hKL
  simpa [hEq] using hLcount