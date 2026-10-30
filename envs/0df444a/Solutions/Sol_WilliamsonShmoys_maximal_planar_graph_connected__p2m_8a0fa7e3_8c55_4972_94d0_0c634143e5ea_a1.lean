-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_connected__p2m_8a0fa7e3_8c55_4972_94d0_0c634143e5ea_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T11:59:26.209374+00:00
-- url     : https://prove2.me/submissions/5b959f8b-0a3e-429a-bff4-184b09275177
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_exists_planar_strict_supergraph_of_disconnected__p2m_0d71806b_1bff_4247_911b_0bb3ff02c978_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : LE.le 3 (Fintype.card V))
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset H.edgeSet K.edgeSet -> K.edgeSet = H.edgeSet) :
    H.Connected := by
  by_contra hdis
  have hExt :=
    WilliamsonShmoys.exists_planar_strict_supergraph_of_disconnected__p2m_0d71806b_1bff_4247_911b_0bb3ff02c978_a1
      H hH hV hdis
  exact Exists.elim hExt (fun K hKdata =>
    hKdata.right.right (hmax K hKdata.left hKdata.right.left))