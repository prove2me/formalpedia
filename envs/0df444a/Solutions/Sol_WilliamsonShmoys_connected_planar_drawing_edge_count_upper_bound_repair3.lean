-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_count_upper_bound_repair3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:38:33.126638+00:00
-- url     : https://prove2.me/submissions/9598f25e-8770-49c1-84b9-f32927d6de7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_repair3
import Theorems.Thm_WilliamsonShmoys_edge_set_ncard_mono

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hconn : T.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hH, hsub, hmax⟩ :=
    WilliamsonShmoys.planar_graph_maximal_extension T hT hconn hCard
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count_repair3 H hH hmax hCard
  have hmono := WilliamsonShmoys.edge_set_ncard_mono T H hsub
  omega
