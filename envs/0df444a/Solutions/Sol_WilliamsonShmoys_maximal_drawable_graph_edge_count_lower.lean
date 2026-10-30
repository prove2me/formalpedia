-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_lower
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:51:11.287517+00:00
-- url     : https://prove2.me/submissions/2be30bfc-12e4-43aa-8465-e4ca0c258034

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
  obtain ⟨U, hTU, hU, hbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count_lower T hV hT
  have hEq : U = T := hmax U hTU hU
  simpa [hEq] using hbound