-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_261600ee_7fa4_4a45_a37b_002442c9d475_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:27:16.244168+00:00
-- url     : https://prove2.me/submissions/8a8ccfe9-6023-424a-83fb-bcc5964111e9

import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_extension_f1f92bb7_maximal_supergraph_edge_count

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.drawable_triangulation_extension_f1f92bb7_maximal_supergraph_edge_count M hM hMax hCard