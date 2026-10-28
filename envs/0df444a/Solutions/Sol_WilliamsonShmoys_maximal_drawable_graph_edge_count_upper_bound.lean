-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:47:05.405877+00:00
-- url     : https://prove2.me/submissions/1376b517-c6f6-4b0d-8c53-a7c3d06655fb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_for_4be75fe8
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_exact_for_4be75fe8
import Theorems.Thm_SimpleGraph_edgeSet_ncard_mono_for_4be75fe8

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  let hExt :=
    WilliamsonShmoys.planar_drawingOn_maximal_extension_for_4be75fe8 K hV hK
  let M := Classical.choose hExt
  have hMprops := Classical.choose_spec hExt
  have hKM : K <= M := hMprops.1
  have hMdraw : HasPlanarDrawingOn M := hMprops.2.1
  have hMax :
      forall H : SimpleGraph V, M <= H -> HasPlanarDrawingOn H -> H = M :=
    hMprops.2.2
  have hCount :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count_exact_for_4be75fe8
      M hV hMdraw hMax
  calc
    K.edgeSet.ncard <= M.edgeSet.ncard :=
      SimpleGraph.edgeSet_ncard_mono_for_4be75fe8 K M hKM
    _ = 3 * Fintype.card V - 6 := hCount