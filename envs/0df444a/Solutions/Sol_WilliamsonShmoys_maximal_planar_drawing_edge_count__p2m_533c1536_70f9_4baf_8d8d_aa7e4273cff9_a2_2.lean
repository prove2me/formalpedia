-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_533c1536_70f9_4baf_8d8d_aa7e4273cff9_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:43:37.346425+00:00
-- url     : https://prove2.me/submissions/91060f16-eea7-42aa-b07f-afb291b9fd0e

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1 H hH hcard hmax