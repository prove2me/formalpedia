-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:35:49.010057+00:00
-- url     : https://prove2.me/submissions/a3c87bcf-5272-4a5c-ae95-b8fe831cfef3

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_e69220cf_5cc1_4342_a84f_9ccd3d593737_a7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) : 3 * Fintype.card V - 6 = T.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_edge_count__p2m_e69220cf_5cc1_4342_a84f_9ccd3d593737_a7 T hV hT hmax
