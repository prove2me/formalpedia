-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_graph_exact_edge_count__p2m_fc475467_cefd_44fd_810b_5d1d49565f31_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:36:23.798376+00:00
-- url     : https://prove2.me/submissions/1720f119-b959-4e85-9a4b-401a56fe3b86

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_e69220cf_5cc1_4342_a84f_9ccd3d593737_a7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : 3 * Fintype.card V - 6 = L.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_edge_count__p2m_e69220cf_5cc1_4342_a84f_9ccd3d593737_a7 L hV hL hmax
