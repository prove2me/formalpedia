-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_drawable_extension__p2m_34e3c7ce_8936_45db_894d_7bc025c10cb3_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:21:48.501201+00:00
-- url     : https://prove2.me/submissions/044ece55-2c19-40fb-989f-16d1e21c2d29
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_has_unreachable_pair__p2m_37fa9a5a_5453_43d3_9231_e1df50e08028_a1
import Theorems.Thm_WilliamsonShmoys_drawable_add_edge_between_unreachable_vertices__p2m_37fa9a5a_5453_43d3_9231_e1df50e08028_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ L : SimpleGraph V, K ≤ L ∧ L ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
  obtain ⟨u, v, hUnreachable⟩ :=
    WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_37fa9a5a_5453_43d3_9231_e1df50e08028_a1
      K hcard hDisconnected
  obtain ⟨L, hle, hne, hnew, hDrawing⟩ :=
    WilliamsonShmoys.drawable_add_edge_between_unreachable_vertices__p2m_37fa9a5a_5453_43d3_9231_e1df50e08028_a1
      K hK u v hUnreachable
  exact ⟨L, hle, hne, hDrawing⟩