-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_has_euler_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:52:53.733112+00:00
-- url     : https://prove2.me/submissions/dab62fc9-c36e-445b-8dfc-066c98fcc66d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hKT, hT, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f
      K hV hK
  have hTK : T = K := hmax T hKT hT
  simpa [hTK] using hcount