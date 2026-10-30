-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_upper_bound__p2m_f02ef8ad_5db5_4334_91a0_6b5d944fa80f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:28:54.564063+00:00
-- url     : https://prove2.me/submissions/014c9396-08f6-4e64-9374-e5999347c33a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph__p2m_11b8d141_5db8_4e85_8178_19adf7dd7abd_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_11b8d141_5db8_4e85_8178_19adf7dd7abd_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hH, hconn, hle⟩ :=
    WilliamsonShmoys.connected_planar_supergraph__p2m_11b8d141_5db8_4e85_8178_19adf7dd7abd_a1 K hK hV
  have hbound := WilliamsonShmoys.connected_planar_edge_bound__p2m_11b8d141_5db8_4e85_8178_19adf7dd7abd_a1 H hH hconn hV
  omega