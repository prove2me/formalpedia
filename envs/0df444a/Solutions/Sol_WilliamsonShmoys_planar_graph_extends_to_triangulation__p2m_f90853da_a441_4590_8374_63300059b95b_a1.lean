-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_extends_to_triangulation__p2m_f90853da_a441_4590_8374_63300059b95b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:26:50.11195+00:00
-- url     : https://prove2.me/submissions/6f47b2c2-22c7-48e6-884f-dd48bbf316b4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_f14f4602_64b2_453c_98d9_533a82cb7d04_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_f14f4602_64b2_453c_98d9_533a82cb7d04_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      3 * Fintype.card V - 6 = H.edgeSet.ncard := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    planar_drawing_has_maximal_supergraph__p2m_f14f4602_64b2_453c_98d9_533a82cb7d04_a1 K hK
  exact ⟨H, hKH, hH,
    maximal_planar_graph_edge_count__p2m_f14f4602_64b2_453c_98d9_533a82cb7d04_a1 H hH hmax hV⟩