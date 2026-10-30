-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_simple_graph_edge_count_lower__p2m_a57dc3db_20ea_40d3_9b0f_dcd4c88e6cc2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:45:29.588435+00:00
-- url     : https://prove2.me/submissions/7068b32c-a0e9-4e17-87f0-cce005bb4baa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_triangular_face_counts__p2m_218cb22b_5a70_4242_ad72_2387eb96d6df_a1
import Theorems.Thm_WilliamsonShmoys_euler_triangular_face_count_edge_arithmetic__p2m_218cb22b_5a70_4242_ad72_2387eb96d6df_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, L <= M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_has_euler_triangular_face_counts__p2m_218cb22b_5a70_4242_ad72_2387eb96d6df_a1
      L hDraw hMax hCard
  exact WilliamsonShmoys.euler_triangular_face_count_edge_arithmetic__p2m_218cb22b_5a70_4242_ad72_2387eb96d6df_a1
    f (Fintype.card V) L.edgeSet.ncard hEuler hIncidence