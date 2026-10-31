-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_count_upper__p2m_9f29656c_dc34_4a7a_a3c2_ff1f2fc6d96d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:25:39.588907+00:00
-- url     : https://prove2.me/submissions/c94a3723-92b2-4956-8ffd-3db22521ca0d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_triangulation_supergraph__p2m_e072b4d5_a9ae_4f40_9238_0c277accf09b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hConn : M.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨N, hSub, _hPlanar, hNcard⟩ :=
    WilliamsonShmoys.planar_connected_triangulation_supergraph__p2m_e072b4d5_a9ae_4f40_9238_0c277accf09b_a1
      M hM hConn hCard
  have hle : M.edgeSet.ncard ≤ N.edgeSet.ncard := Set.ncard_mono hSub
  omega