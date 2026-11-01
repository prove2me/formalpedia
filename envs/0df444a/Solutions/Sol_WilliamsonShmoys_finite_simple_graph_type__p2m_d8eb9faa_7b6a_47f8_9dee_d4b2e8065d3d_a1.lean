-- Prove2me | solution 1 for WilliamsonShmoys.finite_simple_graph_type__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:33:24.281781+00:00
-- url     : https://prove2.me/submissions/4d3646b3-0f40-4a9d-9a0c-e82b2ca23050

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance