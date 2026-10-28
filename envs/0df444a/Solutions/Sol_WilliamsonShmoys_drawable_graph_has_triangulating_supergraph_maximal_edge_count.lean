-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulating_supergraph_maximal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:39:07.506496+00:00
-- url     : https://prove2.me/submissions/28c103f3-92ce-4b99-8cca-1d20d82b38f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulating_supergraph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hKT, hTdraw, hcount⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulating_supergraph_edge_count K hV hK
  have hTK : T = K := hmax T hKT hTdraw
  simpa [hTK] using hcount