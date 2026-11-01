-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_fdf6b599_6bc6_49f9_8e7c_aa4a3539064a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:54:42.974593+00:00
-- url     : https://prove2.me/submissions/53b92572-22e3-4c77-b3fc-853ebcf04a1a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_ff0df929_a528_472b_801c_6c58169000bb_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHplanar, hEdges, hHcount⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_ff0df929_a528_472b_801c_6c58169000bb_a1
      G hplanar hconn hcard
  omega