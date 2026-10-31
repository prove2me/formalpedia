-- Prove2me | solution 2 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:16:53.767468+00:00
-- url     : https://prove2.me/submissions/f56a50da-1ccf-4e14-bb11-0f440343575f

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_triangulation_edge_count_exists_maximal_drawable_extension

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ T : SimpleGraph V, L ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T :=
  WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count_exists_maximal_drawable_extension L hL
