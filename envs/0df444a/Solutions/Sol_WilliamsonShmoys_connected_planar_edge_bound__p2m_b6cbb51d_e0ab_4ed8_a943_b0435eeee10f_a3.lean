-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_b6cbb51d_e0ab_4ed8_a943_b0435eeee10f_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:21.279849+00:00
-- url     : https://prove2.me/submissions/5c8eab8e-1a5d-4147-85fb-e715b5c47e54
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_bound__p2m_eac4b030_cd26_487c_98af_ec9d769936c5_a1
import Theorems.Thm_WilliamsonShmoys_subgraph_edgeSet_ncard_mono__p2m_eac4b030_cd26_487c_98af_ec9d769936c5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M H : SimpleGraph V)
    (hMH : M ≤ H)
    (hHconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hmono :=
    WilliamsonShmoys.subgraph_edgeSet_ncard_mono__p2m_eac4b030_cd26_487c_98af_ec9d769936c5_a1
      M H hMH
  have hplanar :=
    WilliamsonShmoys.connected_planar_graph_edge_bound__p2m_eac4b030_cd26_487c_98af_ec9d769936c5_a1
      H hHconn hHdraw hV
  omega
