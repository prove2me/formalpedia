-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_13012d9d_6550_4fe7_b932_cfc62eea8364_a4
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:28:21.723512+00:00
-- url     : https://prove2.me/submissions/96056af7-a478-4263-80bd-9eac986ac678

import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_count

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.exists_planar_supergraph_edge_count M hV hM